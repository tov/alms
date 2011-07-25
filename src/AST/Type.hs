{-# LANGUAGE TypeFamilies #-}
module AST.Type (
  -- * Types
  Quant(..), Type'(..), Type, TyPat'(..), TyPat,
  -- ** Constructors
  tyApp, tyVar, tyFun, tyQu, tyMu, tyRow, tyAnti,
  tpVar, tpApp, tpRow, tpAnti,
  TyAppN(..),

  -- * Built-in types
  tyUnit, tyRowEnd, tyVariant, tyRecord, tyRowDots, tyRowMap, tyRowHole,
  tyTuple, tyUn, tyAf,
  -- ** Type construtor names
  tnUnit, tnRowEnd, tnVariant, tnRecord, tnRowDots, tnRowMap, tnRowHole,
  tnTuple, tnUn, tnAf,
  -- ** Convenience constructors
  tyArr, tyLol,
  tyAll, tyEx,
  tyRecordAdditive, tyRecordMultiplicative,

  -- * Miscellany
  dumpType
) where

import Util
import Meta.DeriveNotable
import AST.Notable
import AST.Anti
import AST.Kind
import AST.Ident
import qualified Syntax.Strings as Strings

import Prelude ()
import Data.Generics (Typeable, Data)

-- | Type quantifers
data Quant = Forall | Exists | QuantAnti Anti
  deriving (Typeable, Data, Eq, Ord)

type Type i  = Located Type' i
type TyPat i = Located TyPat' i

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type' i
  = TyApp  (QTypId i) [Type i]
  | TyVar  (TyVar i)
  | TyFun  (Type i) (Maybe (QExp i)) (Type i)
  | TyQu   Quant (TyVar i) (Type i)
  | TyMu   (TyVar i) (Type i)
  | TyRow  (Uid i) (Type i) (Type i)
  | TyAnti Anti
  deriving (Typeable, Data)

-- | Type patterns for defining type operators
data TyPat' i
  -- | type variables
  = TpVar (TyVar i) Variance
  -- | type constructor applications
  | TpApp (QTypId i) [TyPat i]
  -- | each element of a row
  | TpRow (TyVar i) Variance
  -- | antiquotes
  | TpAnti Anti
  deriving (Typeable, Data)

deriveNotable ''Type
deriveNotable ''TyPat

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar i -> Type i -> Type i
tyAll = tyQu Forall
tyEx  = tyQu Exists

tyArr         :: Type i -> Type i -> Type i
tyArr          = tyFun <-> Nothing

tyLol         :: Type i -> Type i -> Type i
tyLol          = tyFun <-> Just maxBound

infixr 8 `tyArr`, `tyLol`

instance Show Quant where
  show Forall        = Strings.all
  show Exists        = Strings.ex
  show (QuantAnti a) = show a

---
--- Built-in types
---

-- | Names of built-in types
tnUnit, tnRowEnd, tnVariant, tnRecord, tnRowDots, tnRowMap, tnRowHole,
  tnTuple, tnUn, tnAf :: String

tnUnit         = "INTERNALS.PrimTypes.unit"
tnRowEnd       = "INTERNALS.PrimTypes.rowend"
tnVariant      = "INTERNALS.PrimTypes.variant"
tnRecord       = "INTERNALS.PrimTypes.record"
tnRowDots      = "rowdots#"
tnRowMap       = "rowmap#"
tnRowHole      = "rowhole#"
tnTuple        = "INTERNALS.PrimTypes.*"
tnUn           = "INTERNALS.PrimTypes.unlimited"
tnAf           = "INTERNALS.PrimTypes.affine"

--- Convenience constructors

-- Types

-- | Class defining variadic function 'tyAppN' for constructing
--   type constructor applications.
class TyApp' r i ⇒ TyAppN n r i | r → i where
  tyAppN ∷ n → r

instance TyApp' r i ⇒ TyAppN (Path (ModId i) (TypId i)) r i where
  tyAppN ql = tyApp' ql []

instance TyApp' r i ⇒ TyAppN (TypId i) r i where
  tyAppN l = tyApp' (J [] l) []

instance (Tag i, TyApp' r i) ⇒ TyAppN String r i where
  tyAppN s = tyApp' (qident s) []

-- | Helper class for @TyApp'@.
class TyApp' r i | r → i where
  tyApp' ∷ QTypId i → [Type i] → r

instance TyApp' (Type i) i where
  tyApp' = tyApp

instance (TyApp' r i, a ~ Type i) ⇒ TyApp' (a → r) i where
  tyApp' ql ts t = tyApp' ql (ts++[t])

tyUnit        :: Tag i => Type i
tyUnit         = tyAppN tnUnit

tyRowEnd      :: Tag i => Type i
tyRowEnd       = tyAppN tnRowEnd

tyVariant     :: Tag i => Type i -> Type i
tyVariant      = tyAppN tnVariant

tyRecord      :: Tag i => Type i -> Type i -> Type i
tyRecord       = tyAppN tnRecord

tyRowDots     :: Tag i => Type i -> Type i
tyRowDots      = tyAppN tnRowDots

tyRowMap      :: Tag i => Type i -> Type i -> Type i
tyRowMap       = tyAppN tnRowMap

tyRowHole     :: Tag i => Type i -> Type i
tyRowHole      = tyAppN tnRowHole

tyTuple       :: Tag i => Type i -> Type i -> Type i
tyTuple        = tyAppN tnTuple

tyUn          :: Tag i => Type i
tyUn           = tyAppN tnUn

tyAf          :: Tag i => Type i
tyAf           = tyAppN tnAf

tyRecordAdditive, tyRecordMultiplicative :: Tag i => Type i -> Type i
tyRecordAdditive       = tyRecord tyAf
tyRecordMultiplicative = tyRecord tyUn

---
--- Debugging
---

-- | Noisy type printer for debugging
dumpType :: Tag i => Int -> Type i -> IO ()
dumpType i0 nt0 = do
  putStr (replicate i0 ' ')
  noIndent i0 nt0
  where
  noIndent i nt@(N _ t0) =
    case t0 of
      TyApp n ps -> do
        putStrLn $ show n ++ " {"
        mapM_ (dumpType (i + 2)) ps
        putStrLn (replicate i ' ' ++ "}")
      TyFun dom mq cod -> do
        putStrLn $ case mq of
          Just q  -> "-[" ++ dumpQExp q ++ "]> {"
          Nothing -> "-> {"
        dumpType (i + 2) dom
        dumpType (i + 2) cod
        putStrLn (replicate i ' ' ++ "}")
      TyVar tv -> print tv
      TyQu u a t -> do
        print $ show u ++ " " ++ show a ++ ". {"
        dumpType (i + 2) t
        putStrLn (replicate i ' ' ++ "}")
      TyMu a t -> do
        print $ "mu " ++ show a ++ ". {"
        dumpType (i + 2) t
        putStrLn (replicate i ' ' ++ "}")
      TyRow _ _ _ -> do
        putStr "ro"
        dumpRow (i + 2) 'w' nt
      TyAnti a -> do
        print a
  --
  dumpRow i c (N _ (TyRow n t1 t2)) = do
    let lab = show n
    putStr (c:' ':lab++": ")
    noIndent (i + length lab + 4) t1
    putStr (replicate i ' ')
    dumpRow i '|' t2
  dumpRow i c t = do
    putStr (c:" ")
    noIndent (i + 2) t
  --
  dumpQExp (N _ q0) = case q0 of
    QeLit ql       → show ql
    QeVar tv       → show tv
    QeJoin qe1 qe2 → dumpQExp qe1 ++ ',' : dumpQExp qe2
    QeAnti _       → "ANTI"


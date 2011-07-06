{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      FunctionalDependencies,
      MultiParamTypeClasses,
      ParallelListComp,
      TypeSynonymInstances,
      TemplateHaskell,
      TupleSections,
      TypeFamilies,
      UndecidableInstances,
      UnicodeSyntax #-}
module Syntax.Type (
  -- * Types
  Quant(..), Type'(..), Type, TyPat'(..), TyPat,
  -- ** Type annotations
  Annot,
  -- ** Constructors
  tyApp, tyVar, tyFun, tyQu, tyMu, tyRow, tyAnti,
  tpVar, tpApp, tpAnti,
  TyAppN(..),

  -- * Built-in types
  tyUnit, tyTuple, tyUn, tyAf,
  -- ** Convenience constructors
  tyArr, tyLol,
  tyAll, tyEx,

  -- * Miscellany
  dumpType
) where

import Util
import Meta.DeriveNotable
import Syntax.Notable
import Syntax.Anti
import Syntax.Kind
import Syntax.Ident
import qualified Syntax.Strings as Strings

import Prelude ()
import Data.Generics (Typeable, Data)
import qualified Data.Map as M

-- | Type quantifers
data Quant = Forall | Exists | QuantAnti Anti
  deriving (Typeable, Data, Eq, Ord)

type Type i  = Located Type' i
type TyPat i = Located TyPat' i

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type' i
  = TyApp  (QLid i) [Type i]
  | TyVar  (TyVar i)
  | TyFun  (Maybe (QExp i)) (Type i) (Type i)
  | TyQu   Quant (TyVar i) (Type i)
  | TyMu   (TyVar i) (Type i)
  | TyRow  (BIdent i) (Type i) (Type i)
  | TyAnti Anti
  deriving (Typeable, Data)

-- | Type patterns for defining type operators
data TyPat' i
  -- | type variables
  = TpVar (TyVar i) Variance
  -- | type constructor applications
  | TpApp (QLid i) [TyPat i]
  -- | antiquotes
  | TpAnti Anti
  deriving (Typeable, Data)

deriveNotable ''Type
deriveNotable ''TyPat

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar i -> Type i -> Type i
tyAll = tyQu Forall
tyEx  = tyQu Exists

instance Show Quant where
  show Forall        = Strings.all
  show Exists        = Strings.ex
  show (QuantAnti a) = show a

---
--- Built-in types
---

--- Convenience constructors

-- | Class defining variadic function 'tyAppN' for constructing
--   type constructor applications.
class TyApp' r i ⇒ TyAppN n r i | r → i where
  tyAppN ∷ n → r

instance TyApp' r i ⇒ TyAppN (QLid i) r i where
  tyAppN ql = tyApp' ql []

instance TyApp' r i ⇒ TyAppN (Lid i) r i where
  tyAppN l = tyApp' (J [] l) []

instance TyApp' r i ⇒ TyAppN String r i where
  tyAppN s = tyApp' (qlid s) []

-- | Helper class for @TyApp'@.
class Id i ⇒ TyApp' r i | r → i where
  tyApp' ∷ QLid i → [Type i] → r

instance Id i ⇒ TyApp' (Type i) i where
  tyApp' = tyApp

instance (TyApp' r i, a ~ Type i) ⇒ TyApp' (a → r) i where
  tyApp' ql ts t = tyApp' ql (ts++[t])

tyUnit        :: Id i => Type i
tyUnit         = tyAppN "unit"

tyTuple       :: Id i => Type i -> Type i -> Type i
tyTuple        = tyAppN "*"

tyUn          :: Id i => Type i
tyUn           = tyAppN "U"

tyAf          :: Id i => Type i
tyAf           = tyAppN "A"

tyArr         :: Type i -> Type i -> Type i
tyArr          = tyFun Nothing

tyLol         :: Type i -> Type i -> Type i
tyLol          = tyFun (Just maxBound)

infixr 8 `tyArr`, `tyLol`

---
--- Type annotations
---

-- | A type annotation is merely a syntactic type
type Annot i = Type i

instance Id i ⇒ AnnotTV (QExp' i) i where
  annotTVsWith f qe0 = case qe0 of
    QeLit _        → mempty
    QeVar tv       → M.singleton tv mempty
    QeJoin qe1 qe2 → annotTVsWith f (qe1, qe2)
    QeAnti _       → mempty

instance Id i ⇒ AnnotTV (Type' i) i where
  annotTVsWith f t0 = case t0 of
    TyApp ql ts    →
      mconcat
        [ f ql ix <$> annotTVsWith f t
        | t  ← ts
        | ix ← [ 1 .. ] ]
    TyVar tv       → M.singleton tv mempty
    TyFun qe t1 t2 →
      let t1m = f (qlid "->") 1 <$> annotTVsWith f t1
          qem = f (qlid "->") 2 <$> annotTVsWith f qe
          t2m = f (qlid "->") 3 <$> annotTVsWith f t2
       in t1m `mappend` qem `mappend` t2m
    TyQu _ tv t    → M.delete tv (annotTVsWith f t)
    TyMu tv t      → M.delete tv (annotTVsWith f t)
    TyRow _ t1 t2  → annotTVsWith f (t1, t2)
    TyAnti _       → mempty

---
--- Debugging
---

-- | Noisy type printer for debugging
dumpType :: Id i => Int -> Type i -> IO ()
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
      TyFun mq dom cod -> do
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


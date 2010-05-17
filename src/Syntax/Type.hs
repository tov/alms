{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      ParallelListComp,
      TemplateHaskell,
      TypeFamilies #-}
module Syntax.Type (
  -- * Types
  Quant(..), Type'(..), Type,
  -- ** Constructors
  tyApp, tyVar, tyFun, tyQu, tyMu, tyAnti,

  -- * Built-in types
  tyNulOp, tyUnOp, tyBinOp,
  tyUnit, tyTuple, tyUn, tyAf,
  -- ** Convenience constructors
  tyArr, tyLol,
  tyAll, tyEx,

  -- * Miscellany
  dumpType
) where

import Meta.DeriveNotable
import Syntax.Notable
import Syntax.Anti
import Syntax.Kind
import Syntax.Ident

import Data.Generics (Typeable, Data)

-- | Type quantifers
data Quant = Forall | Exists | QuantAnti Anti
  deriving (Typeable, Data, Eq, Ord)

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type' i
  = TyApp  (QLid i) [Type i]
  | TyVar  TyVar
  | TyFun  (QExp TyVar) (Type i) (Type i)
  | TyQu   Quant TyVar (Type i)
  | TyMu   TyVar (Type i)
  | TyAnti Anti
  deriving (Typeable, Data)

type Type i = Located Type' i

deriveNotable ''Type

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar -> Type i -> Type i
tyAll = tyQu Forall
tyEx  = tyQu Exists

instance Show Quant where
  show Forall = "all"
  show Exists = "ex"
  show (QuantAnti a) = show a

---
--- Built-in types
---

--- Convenience constructors

tyNulOp       :: Id i => String -> Type i
tyNulOp s      = tyApp (qlid s) []

tyUnOp        :: Id i => String -> Type i -> Type i
tyUnOp s a     = tyApp (qlid s) [a]

tyBinOp       :: Id i => String -> Type i -> Type i -> Type i
tyBinOp s a b  = tyApp (qlid s) [a, b]

tyUnit        :: Id i => Type i
tyUnit         = tyNulOp "unit"

tyTuple       :: Id i => Type i -> Type i -> Type i
tyTuple        = tyBinOp "*"

tyUn          :: Id i => Type i
tyUn           = tyNulOp "U"

tyAf          :: Id i => Type i
tyAf           = tyNulOp "A"

tyArr         :: Type i -> Type i -> Type i
tyArr          = tyFun minBound

tyLol         :: Type i -> Type i -> Type i
tyLol          = tyFun maxBound

infixr 8 `tyArr`, `tyLol`

-- | Noisy type printer for debugging
dumpType :: Int -> Type i -> IO ()
dumpType i (N _ t0) = do
  putStr (replicate i ' ')
  case t0 of
    TyApp n ps -> do
      putStrLn $ show n ++ " {"
      mapM_ (dumpType (i + 2)) ps
      putStrLn (replicate i ' ' ++ "}")
    TyFun q dom cod -> do
      putStrLn $ "-[" ++ maybe "ANTI" show (qInterpretM q) ++ "]> {"
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
    TyAnti a -> do
      print a


{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      ParallelListComp #-}
module Syntax.Type (
  -- * Types
  Quant(..), Type(..),
  -- ** Accessors and updaters
  tycon, tyargs, setTycon,

  -- * Built-in types
  tyNulOp, tyUnOp, tyBinOp,
  tyUnit, tyTuple, tyUn, tyAf,
  -- ** Convenience constructors
  tyArr, tyLol,
  tyAll, tyEx,

  -- * Miscellany
  dumpType
) where

import Syntax.Anti
import Syntax.Kind
import Syntax.Ident

import Data.Generics (Typeable, Data)

-- | Type quantifers
data Quant = Forall | Exists | QuantAnti Anti
  deriving (Typeable, Data, Eq, Ord)

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type i = TyApp  QLid [Type i]
            | TyVar  TyVar
            | TyFun  (QExp TyVar) (Type i) (Type i)
            | TyQu   Quant TyVar (Type i)
            | TyMu   TyVar (Type i)
            | TyAnti Anti
  deriving (Typeable, Data)

tycon :: Type i -> QLid
tycon (TyApp tc _)  = tc
tycon _             = error "tycon: not a TyApp"
tyargs :: Type i -> [Type i]
tyargs (TyApp _ ts) = ts
tyargs _            = error "tyargs: not a TyApp"

setTycon :: Type i -> QLid -> Type i
setTycon (TyApp _ ts) tc = TyApp tc ts
setTycon t _             = t

infixl `setTycon`

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar -> Type i -> Type i
tyAll = TyQu Forall
tyEx  = TyQu Exists

instance Show Quant where
  show Forall = "all"
  show Exists = "ex"
  show (QuantAnti a) = show a

---
--- Built-in types
---

--- Convenience constructors

tyNulOp       :: String -> Type i
tyNulOp s      = TyApp (qlid s) []

tyUnOp        :: String -> Type i -> Type i
tyUnOp s a     = TyApp (qlid s) [a]

tyBinOp       :: String -> Type i -> Type i -> Type i
tyBinOp s a b  = TyApp (qlid s) [a, b]

tyUnit        :: Type i
tyUnit         = tyNulOp "unit"

tyTuple       :: Type i -> Type i -> Type i
tyTuple        = tyBinOp "*"

tyUn          :: Type i
tyUn           = tyNulOp "U"

tyAf          :: Type i
tyAf           = tyNulOp "A"

tyArr         :: Type i -> Type i -> Type i
tyArr          = TyFun minBound

tyLol         :: Type i -> Type i -> Type i
tyLol          = TyFun maxBound

infixr 8 `tyArr`, `tyLol`

-- | Noisy type printer for debugging
dumpType :: Int -> Type i -> IO ()
dumpType i t0 = do
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


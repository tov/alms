{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      ParallelListComp #-}
module Syntax.Type (
  -- * Types
  TyTag(..), Quant(..),
  Type(..), TypeT,
  -- ** Synthetic constructors
  tyAll, tyEx,
  -- ** Accessors and updaters
  tycon, tyargs, tyinfo,
  setTycon, setTyinfo,

  -- * Built-in types
  -- ** Type information
  tdUnit, tdInt, tdFloat, tdString, tdExn,
  tdUn, tdAf, tdFun, tdTuple,
  getTdByName,
  -- ** Session types
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,
  -- ** Convenience type constructors
  tyNulOp, tyUnOp, tyBinOp,
  tyUn, tyAf, tyFun, tyArr, tyLol, tyTuple,
  tyNulOpT, tyUnOpT, tyBinOpT,
  tyUnitT, tyUnT, tyAfT, tyFunT, tyArrT, tyLolT,
  tyTupleT, tyExnT,
  -- ** Type tag queries
  castableType,

  -- * Miscellany
  dumpType
) where

import Syntax.Anti
import Syntax.Kind
import Syntax.Ident

import Data.Generics (Typeable, Data)

-- | Info about a type constructor
data TyTag =
  TyTag {
    -- Identity
    ttId    :: Integer,
    -- The variance of each of its parameters
    ttArity :: [Variance],
    -- Determines qualifier as above
    ttQual  :: QualSet,
    -- upper qualifier bounds for parameters
    ttBound :: [Q]
  }
  |
  TyTagAnti {
    -- Type tag antiquote
    ttAnti :: Anti
  }
  deriving (Show, Typeable, Data)

-- | Type quantifers
data Quant = Forall | Exists | QuantAnti Anti
  deriving (Typeable, Data, Eq)

-- | Types are parameterized by [@i@], the type of information
--   associated with each tycon
data Type i = TyCon  QLid [Type i] i
            | TyVar  TyVar
            | TyQu   Quant TyVar (Type i)
            | TyMu   TyVar (Type i)
            | TyAnti Anti
  deriving (Typeable, Data)

-- | A type-checked type (has tycon info)
type TypeT    = Type TyTag

tycon :: Type i -> QLid
tycon (TyCon tc _ _)  = tc
tycon _               = error "tycon: not a TyCon"
tyargs :: Type i -> [Type i]
tyargs (TyCon _ ts _) = ts
tyargs _              = error "tyargs: not a TyCon"
tyinfo :: Type i -> i
tyinfo (TyCon _ _ i)  = i
tyinfo _              = error "tyinfo: not a TyCon"

setTycon :: Type i -> QLid -> Type i
setTycon (TyCon _ ts i) tc = TyCon tc ts i
setTycon t _               = t
setTyinfo :: Type i -> i -> Type i
setTyinfo (TyCon tc ts _) i = TyCon tc ts i
setTyinfo t _               = t

infixl `setTycon`, `setTyinfo`

-- | Convenience constructors for qualified types
tyAll, tyEx :: TyVar -> Type i -> Type i
tyAll = TyQu Forall
tyEx  = TyQu Exists

instance Eq TyTag where
  td == td' = ttId td == ttId td'

instance Show Quant where
  show Forall = "all"
  show Exists = "ex"
  show (QuantAnti a) = show a

---
--- Built-in types
---

tdUnit, tdInt, tdFloat, tdString,
  tdUn, tdAf, tdFun, tdExn, tdTuple :: TyTag

tdUnit       = TyTag (-1)  []          minBound  []
tdInt        = TyTag (-2)  []          minBound  []
tdFloat      = TyTag (-3)  []          minBound  []
tdString     = TyTag (-4)  []          minBound  []
tdUn         = TyTag (-5)  []          minBound  []
tdAf         = TyTag (-6)  []          maxBound  []
tdFun        = TyTag (-7)  [1, -1, 1]  qualSet   (replicate 3 maxBound)
  where qualSet = QualSet minBound [0]
tdExn        = TyTag (-8)  []          maxBound  []
tdTuple      = TyTag (-9)  [1, 1]      qualSet   [maxBound, maxBound]
  where qualSet = QualSet minBound [0, 1]

tdDual, tdSend, tdRecv, tdSelect, tdFollow :: TyTag
-- For session types:
tdDual       = TyTag (-11) [-1] minBound []
tdSend       = TyTag (-12) [1]  minBound [maxBound]
tdRecv       = TyTag (-13) [-1] minBound [maxBound]
tdSelect     = TyTag (-14) [1]  minBound [minBound]
tdFollow     = TyTag (-15) [1]  minBound [minBound]

getTdByName :: String -> Maybe TyTag
getTdByName name = case name of
  "unit" -> Just tdUnit
  "int" -> Just tdInt
  "float" -> Just tdFloat
  "string" -> Just tdString
  "u" -> Just tdUn
  "a" -> Just tdAf
  "fun" -> Just tdFun
  "exn" -> Just tdExn
  "tuple" -> Just tdTuple
  "dual" -> Just tdDual
  "send" -> Just tdSend
  "recv" -> Just tdRecv
  "select" -> Just tdSelect
  "follow" -> Just tdFollow
  _ -> Nothing

--- Convenience constructors

tyNulOp       :: String -> Type ()
tyNulOp s      = TyCon (qlid s) [] ()

tyUnOp        :: String -> Type () -> Type ()
tyUnOp s a     = TyCon (qlid s) [a] ()

tyBinOp       :: String -> Type () -> Type () -> Type ()
tyBinOp s a b  = TyCon (qlid s) [a, b] ()

tyAf          :: Type ()
tyAf           = tyNulOp "A"

tyUn          :: Type ()
tyUn           = tyNulOp "U"

tyFun         :: Type () -> Type () -> Type () -> Type ()
tyFun q a b    = TyCon (qlid "-[]>") [q, a, b] ()

tyArr         :: Type () -> Type () -> Type ()
tyArr          = tyFun tyUn

tyLol         :: Type () -> Type () -> Type ()
tyLol          = tyFun tyAf

tyTuple       :: Type () -> Type () -> Type ()
tyTuple        = tyBinOp "*"

tyNulOpT       :: i -> String -> Type i
tyNulOpT i s    = TyCon (qlid s) [] i

tyUnOpT        :: i -> String -> Type i -> Type i
tyUnOpT i s a   = TyCon (qlid s) [a] i

tyBinOpT       :: i -> String -> Type i -> Type i -> Type i
tyBinOpT i s a b = TyCon (qlid s) [a, b] i

tyUnitT        :: TypeT
tyUnitT         = tyNulOpT tdUnit "unit"

tyAfT         :: TypeT
tyAfT          = tyNulOpT tdAf "A"

tyUnT         :: TypeT
tyUnT          = tyNulOpT tdUn "U"

tyFunT        :: TypeT -> TypeT -> TypeT -> TypeT
tyFunT q a b   = TyCon (qlid "-[]>") [q, a, b] tdFun

tyArrT        :: TypeT -> TypeT -> TypeT
tyArrT         = tyFunT tyUnT

tyLolT        :: TypeT -> TypeT -> TypeT
tyLolT         = tyFunT tyAfT

tyTupleT       :: TypeT -> TypeT -> TypeT
tyTupleT        = tyBinOpT tdTuple "*"

tyExnT         :: TypeT
tyExnT          = tyNulOpT tdExn "exn"

infixr 8 `tyArr`, `tyLol`, `tyArrT`, `tyLolT`
infixl 7 `tyTuple`, `tyTupleT`

-- | Is the type promotable to a lower-qualifier type?
castableType :: TypeT -> Bool
castableType (TyVar _)         = False
castableType (TyCon _ _ td)    = td == tdFun
castableType (TyQu _ _ t)      = castableType t
castableType (TyMu _ t)        = castableType t
castableType (TyAnti a)        = antierror "castableType" a

-- | Noisy type printer for debugging (includes type tags that aren't
--   normally pretty-printed)
dumpType :: Int -> TypeT -> IO ()
dumpType i t0 = do
  putStr (replicate i ' ')
  case t0 of
    TyCon n ps td -> do
      putStrLn $ show n ++ " [" ++ show td ++ "] {"
      mapM_ (dumpType (i + 2)) ps
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

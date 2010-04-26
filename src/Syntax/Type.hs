{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      ParallelListComp #-}
module Syntax.Type (
  -- * Types
  TyTag(..), Quant(..),
  Type(..), TypeT, TypeTEq(..),
  -- ** Synthetic constructors
  tyAll, tyEx,
  -- ** Accessors and updaters
  tycon, tyargs, tyinfo,
  setTycon, setTyinfo,

  -- * Type operations
  -- ** Freshness
  Ftv(..), FtvVs(..), freshTyVar, freshTyVars,
  -- ** Substitutions
  tysubst, tysubsts,
  -- ** Queries and conversions
  qualifier, replaceTyTags, removeTyTags,

  -- * Built-in types
  -- ** Type information
  tdUnit, tdInt, tdFloat, tdString, tdExn,
  tdArr, tdLol, tdTuple,
  getTdByName,
  -- ** Session types
  dualSessionType,
  tdDual, tdSend, tdRecv, tdSelect, tdFollow,
  -- ** Convenience type constructors
  tyNulOp, tyUnOp, tyBinOp,
  tyArr, tyLol, tyTuple,
  tyNulOpT, tyUnOpT, tyBinOpT,
  tyUnitT, tyArrT, tyLolT, tyTupleT, tyExnT,
  -- ** Type tag queries
  funtypes, castableType,

  -- * Miscellany
  dumpType
) where

import Syntax.Anti
import Syntax.POClass
import Syntax.Kind
import Syntax.Ident
import Util

import Control.Monad.State (State, evalState, get, put)
import Data.Char (isDigit)
import Data.Generics (Typeable(..), Data(..), everywhere, mkT)
import qualified Data.Map as M
import qualified Data.Set as S

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

-- | Remove tycon information from a type
removeTyTags :: Type i -> Type ()
removeTyTags  = untype where
  untype :: Type i -> Type ()
  untype (TyCon con args _) = TyCon con (map untype args) ()
  untype (TyVar tv)         = TyVar tv
  untype (TyQu quant tv t)  = TyQu quant tv (untype t)
  untype (TyMu tv t)        = TyMu tv (untype t)
  untype (TyAnti a)         = antierror "removeTyTags" a

-- | Given a type tag and something traversable, find all type tags
--   with the same identity as the given type tag, and replace them.
--   (We use this to do type abstraction, since we can replace datatype
--   type tags with abstract type tags that have the datacons redacted.)
replaceTyTags :: Data a => TyTag -> a -> a
replaceTyTags tag' = everywhere (mkT each) where
  each :: TyTag -> TyTag
  each tag | ttId tag == ttId tag' = tag'
           | otherwise             = tag

-- | Find the qualifier of a type (which must be decorated with
--   tycon info)
qualifier     :: TypeT -> Q
qualifier (TyCon _ ps td) = bigVee qs' where
  qs  = map qualifier ps
  qs' = q : map (qs !!) ixs
  QualSet q ixs = ttQual td
qualifier (TyVar (TV _ q))   = q
qualifier (TyQu _ _ t)       = qualifier t
qualifier (TyMu _ t)         = qualifier t
qualifier (TyAnti a)         = antierror "qualifier" a

-- | Class for getting free type variables (from types, expressions,
-- lists thereof, pairs thereof, etc.)
class Ftv a where
  ftv :: a -> S.Set TyVar

instance Ftv (Type i) where
  ftv (TyCon _ ts _) = S.unions (map ftv ts)
  ftv (TyVar tv)     = S.singleton tv
  ftv (TyQu _ tv t)  = S.delete tv (ftv t)
  ftv (TyMu tv t)    = S.delete tv (ftv t)
  ftv (TyAnti a)     = antierror "ftv" a

instance Ftv a => Ftv [a] where
  ftv = S.unions . map ftv

instance Ftv TyVar where
  ftv = S.singleton

instance (Ftv a, Ftv b) => Ftv (a, b) where
  ftv (a, b) = ftv a `S.union` ftv b

class FtvVs a where
  ftvVs :: a -> M.Map TyVar Variance

instance FtvVs (Type TyTag) where
  ftvVs (TyCon _ ts td)= M.unionsWith (+)
                         [ M.map (* var) m
                         | var <- ttArity td
                         | m   <- map ftvVs ts ]
  ftvVs (TyVar tv)     = M.singleton tv 1
  ftvVs (TyQu _ tv t)  = M.delete tv (ftvVs t)
  ftvVs (TyMu tv t)    = M.delete tv (ftvVs t)
  ftvVs (TyAnti a)     = antierror "ftvVs" a

instance FtvVs a => FtvVs [a] where
  ftvVs = M.unionsWith (+) . map ftvVs

instance FtvVs TyVar where
  ftvVs tv = M.singleton tv 1

instance (FtvVs a, FtvVs b) => FtvVs (a, b) where
  ftvVs (a, b) = M.unionWith (+) (ftvVs a) (ftvVs b)

freshTyVars :: [TyVar] -> S.Set TyVar -> [TyVar]
freshTyVars tvs0 s0 = loop tvs0 (s0 `S.union` S.fromList tvs0) where
  loop (tv:tvs) s' = let tv' = freshTyVar tv s'
                      in tv' : loop tvs (S.insert tv' s')
  loop _        _ = []

freshTyVar :: TyVar -> S.Set TyVar -> TyVar
freshTyVar tv s = if tv `S.member` s
                    then loop count
                    else tv
  where
    suffix   = reverse . takeWhile isDigit . reverse . unLid $ tvname tv
    prefix   = reverse . dropWhile isDigit . reverse . unLid $ tvname tv
    count    = case reads suffix of
                 ((n, ""):_) -> n
                 _           -> 0
    attach n = tv { tvname = Lid (prefix ++ show n) }
    loop    :: Int -> TyVar
    loop n   =
      let tv' = attach n
      in if tv' `S.member` s
           then loop (n + 1)
           else tv'

-- | Given a list of type variables and types, perform all the
--   substitutions, avoiding capture between them.
tysubsts :: [TyVar] -> [TypeT] -> TypeT -> TypeT
tysubsts ps ts t =
  let ps'     = freshTyVars ps (ftv (t:ts))
      substs tvs ts0 t0 = foldr2 tysubst t0 tvs ts0 in
  substs ps' ts .
    substs ps (map TyVar ps') $
      t

-- | Type substitution (NB: the languages need not match, since
-- types embed in one another)
tysubst :: TyVar -> Type i -> Type i -> Type i
tysubst a t = ts where
  ts (TyVar a')
                = if a' == a
                    then t
                    else TyVar a'
  ts (TyQu u a' t')
                = if a' == a
                    then TyQu u a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyQu u a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyMu a' t')
                = if a' == a
                    then TyMu a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyMu a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyCon c tys td)
                = TyCon c (map ts tys) td
  ts (TyAnti an) = antierror "tysubst" an


instance Eq TyTag where
  td == td' = ttId td == ttId td'

-- | A fresh type for defining alpha equality up to mu.
newtype TypeTEq = TypeTEq { unTypeTEq :: TypeT }

-- | On TypeTEq, we define simple alpha equality, which we then use
-- to keep track of where we've been when we define type equality
-- that understands mu.
instance Eq TypeTEq where
  te1 == te2 = unTypeTEq te1 === unTypeTEq te2
    where
      (===) :: TypeT -> TypeT -> Bool
      TyCon _ ps td === TyCon _ ps' td'
                                 = td == td' && all2 (===) ps ps'
      TyVar x       === TyVar x' = x == x'
      TyQu u x t    === TyQu u' x' t'
        | u == u' && tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      TyMu x t      === TyMu x' t'
        | tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      _             === _        = False

instance Eq (Type TyTag) where
  (==) t1i t2i = evalState (t1i `chk` t2i) [] where
    chk, cmp :: TypeT -> TypeT -> State [(TypeTEq, TypeTEq)] Bool
    t1 `chk` t2 = do
      seen <- get
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      if (te1, te2) `elem` seen
        then return True
        else do
          put ((te1, te2) : (te2, te1) : seen)
          cmp t1 t2

    TyCon _ [p] td `cmp` t
      | td == tdDual                     = dualSessionType p `chk` t
    t              `cmp` TyCon _ [p] td
      | td == tdDual                     = t `chk` dualSessionType p
    TyMu a t       `cmp` t'              = tysubst a (TyMu a t) t `chk` t'
    t'             `cmp` TyMu a t        = t' `chk` tysubst a (TyMu a t) t
    TyCon _ ps td  `cmp` TyCon _ ps' td'
      | td == td'   = allM2 chk ps ps'
    TyVar x        `cmp` TyVar x'        = return (x == x')
    TyQu u x t     `cmp` TyQu u' x' t' 
      | u == u' && tvqual x == tvqual x' = 
        tysubst x a t `chk` tysubst x' a t'
          where a = TyVar (freshTyVar x (ftv [t, t']))
    _            `cmp` _               = return False

instance Show Quant where
  show Forall = "all"
  show Exists = "ex"
  show (QuantAnti a) = show a

-- | The Type partial order
instance PO (Type TyTag) where
  ifMJ bi t1i t2i = clean `liftM` chk [] bi t1i t2i where
    clean :: TypeT -> TypeT
    clean (TyCon c ps td)  = TyCon c (map clean ps) td
    clean (TyVar a)        = TyVar a
    clean (TyQu u a t)     = TyQu u a (clean t)
    clean (TyMu a t)
      | a `S.member` ftv t = TyMu a (clean t)
      | otherwise          = clean t
    clean (TyAnti a)       = antierror "ifMJ" a

    chk, cmp :: Monad m =>
                [((Bool, TypeTEq, TypeTEq), TyVar)] ->
                Bool -> TypeT -> TypeT ->
                m TypeT
    chk seen b t1 t2 = do
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      case lookup (b, te1, te2) seen of
        Just tv -> return (TyVar tv)
        Nothing -> TyMu tv `liftM` cmp seen' b t1 t2 where
          used  = S.fromList (map snd seen)
          tv    = freshTyVar (TV (Lid "r") (qualifier t1 \/ qualifier t2))
                             (ftv [t1, t2] `S.union` used)
          seen' = (((b, te1, te2), tv) : ((b, te2, te1), tv) : seen)

    -- Special cases to treat "all 'a. 'a" as bottom:
    cmp _ b t'@(TyQu Forall tv (TyVar tv')) t
      | tv == tv' && qualifier t <: tvqual tv = return (if b then t else t')
    cmp _ b t t'@(TyQu Forall tv (TyVar tv'))
      | tv == tv' && qualifier t <: tvqual tv = return (if b then t else t')
    -- Special cases for session types duality:
    cmp seen b (TyCon _ [p] td) t
      | td == tdDual                = chk seen b (dualSessionType p) t
    cmp seen b t (TyCon _ [p] td)
      | td == tdDual                = chk seen b t (dualSessionType p)
    -- Special cases for ->/-o subtyping:
    cmp seen b (TyCon _ ps td) (TyCon _ ps' td')
      | (td == tdArr && td' == tdLol) || (td == tdLol && td' == tdArr)
                                    = chk seen b (build ps) (build ps')
          where build ps0 = if b
                              then TyCon (qlid "-o") ps0 tdLol
                              else TyCon (qlid "->") ps0 tdArr
    -- Otherwise:
    cmp seen b (TyCon tc ps td) (TyCon _ ps' td') =
      if td == td' then do
        params <- sequence
          [ case var of
              Covariant     -> chk seen b p p'
              Contravariant -> chk seen (not b) p p'
              _             -> if p == p'
                               then return p
                               else fail "\\/? or /\\?: Does not exist"
             | var <- ttArity td
             | p   <- ps
             | p'  <- ps' ]
        return (TyCon tc params td)
      else fail "\\/? or /\\?: Does not exist"
    cmp seen b (TyQu u a t) (TyQu u' a' t') | u == u' = do
      qual <- ifMJ (not b) (tvqual a) (tvqual a')
      let a1  = a { tvqual = qual } `freshTyVar` (ftv [t, t'])
          t1  = tysubst a (TyVar a1) t
          t'1 = tysubst a' (TyVar a1) t'
      TyQu u a1 `liftM` chk seen b t1 t'1
    cmp seen b (TyMu a t) t' = chk seen b (tysubst a (TyMu a t) t) t'
    cmp seen b t' (TyMu a t) = chk seen b t' (tysubst a (TyMu a t) t)
    cmp _    _ t t' =
      if t == t'
        then return t
        else fail "\\/? or /\\?: Does not exist"

---
--- Built-in types
---

tdUnit, tdInt, tdFloat, tdString,
  tdArr, tdLol, tdExn, tdTuple :: TyTag

tdUnit       = TyTag (-1)  []          minBound  []
tdInt        = TyTag (-2)  []          minBound  []
tdFloat      = TyTag (-3)  []          minBound  []
tdString     = TyTag (-4)  []          minBound  []
tdArr        = TyTag (-5)  [-1, 1]     minBound  [maxBound, maxBound]
tdLol        = TyTag (-6)  [-1, 1]     maxBound  [maxBound, maxBound]
tdExn        = TyTag (-7)  []          maxBound  []
tdTuple      = TyTag (-8)  [1, 1]      qualSet   [maxBound, maxBound]
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
  "arr" -> Just tdArr
  "lol" -> Just tdLol
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

tyArr         :: Type () -> Type () -> Type ()
tyArr          = tyBinOp "->"

tyLol         :: Type () -> Type () -> Type ()
tyLol          = tyBinOp "-o"

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

tyArrT         :: TypeT -> TypeT -> TypeT
tyArrT          = tyBinOpT tdArr "->"

tyLolT         :: TypeT -> TypeT -> TypeT
tyLolT          = tyBinOpT tdLol "-o"

tyTupleT       :: TypeT -> TypeT -> TypeT
tyTupleT        = tyBinOpT tdTuple "*"

tyExnT         :: TypeT
tyExnT          = tyNulOpT tdExn "exn"

infixr 8 `tyArr`, `tyLol`, `tyArrT`, `tyLolT`
infixl 7 `tyTuple`, `tyTupleT`

-- |
-- Helper for finding the dual of a session type (since we can't
-- express this directly in the type system at this point)
dualSessionType :: TypeT -> TypeT
dualSessionType  = d where
  d (TyCon (J [] (Lid ";"))
       [TyCon (J [] (Lid "send")) [ta] _, tr] tdSemi)
    = TyCon (qlid ";") [TyCon (qlid "recv") [ta] tdRecv, d tr] tdSemi
  d (TyCon (J [] (Lid ";"))
       [TyCon (J [] (Lid "recv")) [ta] _, tr] tdSemi)
    = TyCon (qlid ";") [TyCon (qlid "send") [ta] tdSend, d tr] tdSemi
  d (TyCon (J [] (Lid "select"))
       [TyCon (J [] (Lid "+")) [t1, t2] tdSum] _)
    = TyCon (qlid "follow") [TyCon (qlid "+") [d t1, d t2] tdSum] tdFollow
  d (TyCon (J [] (Lid "follow"))
       [TyCon (J [] (Lid "+")) [t1, t2] tdSum] _)
    = TyCon (qlid "select") [TyCon (qlid "+") [d t1, d t2] tdSum] tdSelect
  d (TyMu tv t)
    = TyMu tv (d t)
  d t = t

-- | Constructors for function types
funtypes    :: [TyTag]
funtypes     = [tdArr, tdLol]

-- | Is the type promotable to a lower-qualifier type?
castableType :: TypeT -> Bool
castableType (TyVar _)         = False
castableType (TyCon _ _ td)    = td `elem` funtypes
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

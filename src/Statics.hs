-- | The type checker
{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleContexts,
      FlexibleInstances,
      GeneralizedNewtypeDeriving,
      ImplicitParams,
      MultiParamTypeClasses,
      ParallelListComp,
      PatternGuards,
      QuasiQuotes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances,
      UndecidableInstances,
      ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Statics (
  -- * The type checking monad
  TC, runTC, tcMapM,
  -- * Static environments
  S, env0,
  -- ** Environment construction
  addVal, addType, addMod, addDecl,
  -- * Type checking
  tcProg, tcDecls,
  -- * Type checking results for the REPL
  runTCNew, Module(..), getExnParam, tyConToDec,
  getVarInfo, getTypeInfo, getConInfo,
) where

import Meta.Quasi
import Util
import qualified Syntax
import qualified Syntax.Decl
import qualified Syntax.Expr
import qualified Syntax.Notable
import qualified Syntax.Patt
import Syntax hiding (Type, Type'(..), tyAll, tyEx, tyUn, tyAf,
                      tyTuple, tyUnit, tyArr, tyApp,
                      TyPat, TyPat'(..))
import Loc
import Env as Env
import Ppr ()
import Type
import TypeRel
import Coercion (coerceExpression)

import Control.Monad.RWS    as RWS
import Data.Data (Typeable, Data)
import Data.Generics (everywhere, mkT)
import Data.List (transpose)
import Data.Monoid
import qualified Data.Map as M
import qualified Data.Set as S

import System.IO.Unsafe (unsafePerformIO)
pP :: Show a => a -> b -> b
pP a b = unsafePerformIO (print a) `seq` b
pM :: (Show a, Monad m) => a -> m ()
pM a = if pP a True then return () else fail "wibble"

-- The kind of names we're using.
type R = Renamed

---
--- Type checking environment
---

-- | Mapping from identifiers to value types (includes datacons)
type VE      = Env (BIdent R) Type
-- | Mapping from type constructor names to tycon info
type TE      = Env (Lid R) TyCon
-- | Mapping from module names to modules
type ME      = Env (Uid R) (Module, E)
-- | Mapping from module type names to signatures
type SE      = Env SIGVAR (Module, E)
-- | An environment
data E       = E {
                 vlevel :: VE, -- values
                 tlevel :: TE, -- types
                 mlevel :: ME, -- modules
                 slevel :: SE  -- module types
               }
  deriving (Typeable, Data)

-- | To distinguish signature variables from module variables
--   in overloaded situations
newtype SIGVAR  = SIGVAR { unSIGVAR :: Uid R }
  deriving (Eq, Ord, Typeable, Data)

instance Show SIGVAR where
  showsPrec p (SIGVAR u) = showsPrec p u

-- | A module item is empty, a pair of modules, a value entry (variable
--   or data constructor), a type constructor, or a module.
data Module
  = MdNil
  | MdApp    !Module     !Module
  | MdValue  !(BIdent R) !Type
  | MdTycon  !(Lid R)    !TyCon
  | MdModule !(Uid R)    !Module
  | MdSig    !(Uid R)    !Module
  deriving (Typeable, Data, Show)

-- | Convert an ordered module into an un-ordered environment
envify :: Module -> E
envify MdNil            = genEmpty
envify (MdApp md1 md2)  = envify md1 =+= envify md2
envify (MdValue  x t)   = genEmpty =+= x =:= t
envify (MdTycon  l tc)  = genEmpty =+= l =:= tc
envify (MdModule u md)  = genEmpty =+= u =:= (md, envify md)
envify (MdSig    u md)  = genEmpty =+= SIGVAR u =:= (md, envify md)

instance Monoid Module where
  mempty  = MdNil
  mappend = MdApp

instance Monoid E where
  mempty  = E empty empty empty empty
  mappend (E a1 a2 a3 a4) (E b1 b2 b3 b4)
    = E (a1 =+= b1) (a2 =+= b2) (a3 =+= b3) (a4 =+= b4)

-- Instances for generalizing environment operations over
-- the whole environment structure

instance GenEmpty E where
  genEmpty = mempty

instance GenExtend E E where
  (=+=) = mappend
instance GenExtend E VE where
  e =+= ve' = e =+= E ve' empty empty empty
instance GenExtend E TE where
  e =+= te' = e =+= E empty te' empty empty
instance GenExtend E ME where
  e =+= me' = e =+= E empty empty me' empty
instance GenExtend E SE where
  e =+= se' = e =+= E empty empty empty se'
instance GenLookup E (BIdent R) Type where
  e =..= k = vlevel e =..= k
instance GenLookup E (Lid R) TyCon where
  e =..= k = tlevel e =..= k
instance GenLookup E (Uid R) (Module, E) where
  e =..= k = mlevel e =..= k
instance GenLookup E SIGVAR (Module, E) where
  e =..= k = slevel e =..= k
instance GenLookup E k v =>
         GenLookup E (Path (Uid R) k) v where
  e =..= J []     k = e =..= k
  e =..= J (p:ps) k = do
    (_, e') <- e =..= p
    e' =..= J ps k

---
--- Type checking context and state
---

-- | The type checking context
data Context = Context {
  environment :: !E,
  modulePath  :: ![Uid R]
}

-- | The packaged-up state of the type-checker, which needs to be
--   threaded from one interaction to the next by the REPL
data S   = S {
             -- | The environment
             sEnv    :: E,
             -- | Index for gensyms
             currIx  :: !Int
           }

instance GenLookup E k v =>
         GenLookup Context (Path (Uid R) k) v where
  cxt =..= k = environment cxt =..= k

instance GenExtend Context E where
  cxt =+= e = cxt { environment = environment cxt =+= e }
instance GenExtend Context VE where
  cxt =+= venv = cxt =+= E venv empty empty empty
instance GenExtend Context TE where
  cxt =+= tenv = cxt =+= E empty tenv empty empty
instance GenExtend Context ME where
  cxt =+= menv = cxt =+= E empty empty menv empty
instance GenExtend Context SE where
  cxt =+= senv = cxt =+= E empty empty empty senv

---
--- The type-checking monad
---

-- | The type checking monad reads an environment, writes a module,
--   and keeps track of a gensym counter (currently unused).
newtype TC m a = TC { unTC :: RWST Context Module Int m a }
  deriving (Functor, Monad)

instance Monad m => Applicative (TC m) where
  pure  = return
  (<*>) = ap

instance Monad m => MonadWriter Module (TC m) where
  tell   = TC . tell
  listen = TC . listen . unTC
  pass   = TC . pass . unTC

instance Monad m => MonadReader Context (TC m) where
  ask     = TC ask
  local f = TC . local f . unTC

-- | Like 'ask', but monadic
asksM :: MonadReader r m => (r -> m a) -> m a
asksM  = (ask >>=)

-- | Run a type checking computation with the given initial state,
--   returning the result and the updated state
runTC :: Monad m => S -> TC m a -> m (a, S)
runTC  = liftM prj <$$> runTCNew where
  prj (a, _, s) = (a, s)

-- | Run a type checking computation with the given initial state,
--   returning the result and the updated state
runTCNew :: Monad m => S -> TC m a -> m (a, Module, S)
runTCNew s action = do
  let cxt = Context (sEnv s) []
      ix  = currIx s
  (a, ix', md) <- runRWST (unTC action) cxt ix
  let e'  = sEnv s =+= envify md
  return (a, md, S e' ix')

-- | Generate a fresh integer for use as a 'TyCon' id
newIndex :: Monad m => TC m Int
newIndex = TC $ do
  i <- get
  put (i + 1)
  return i

-- | Add a module to the current module path
enterModule :: Monad m => Uid R -> TC m a -> TC m a
enterModule u = local $ \cxt ->
  cxt { modulePath = u : modulePath cxt }

currentModulePath :: Monad m => TC m [Uid R]
currentModulePath  = asks (reverse . modulePath)

-- | Add a variable binding to the generated module
bindVar :: Monad m => Lid R -> Type -> TC m ()
bindVar l t = tell (MdValue (Var l) t)

-- | Add a data constructor binding to the generated module
bindCon :: Monad m => Uid R -> Type -> TC m ()
bindCon u t = tell (MdValue (Con u) t)

-- | Add a type constructor binding to the generated module
bindTycon :: Monad m => Lid R -> TyCon -> TC m ()
bindTycon l tc = tell (MdTycon l tc)

-- | Add a module binding to the generated module
bindModule :: Monad m => Uid R -> Module -> TC m ()
bindModule u md = tell (MdModule u md)

-- | Add a module type binding to the generated module
bindSig :: Monad m => Uid R -> Module -> TC m ()
bindSig u md = tell (MdSig u md)

-- | Run some computation with the context extended by a module
inModule :: Monad m => Module -> TC m a -> TC m a
inModule md = local (=+= envify md)

-- | Run in the environment consisting of only the given module
onlyInModule :: Monad m => Module -> TC m a -> TC m a
onlyInModule = local (\cxt -> cxt { environment = mempty }) <$$> inModule

-- | Grab the module generated by a computate, and generate the empty
--   module in turn
steal :: Monad m => TC m a -> TC m (a, Module)
steal = censor (const mempty) . listen

-- | Map a function over a list, allowing the exports of each item
--   to be in scope for the rest
tcMapM :: Monad m => (a -> TC m b) -> [a] -> TC m [b]
tcMapM _ []     = return []
tcMapM f (x:xs) = do
  (x', md) <- listen (f x)
  xs' <- inModule md $ tcMapM f xs
  return (x':xs')

{- -- deprecated?
-- | Abstract the given type by removing its datacon or synonym info
withoutConstructors :: Monad m =>
                       TyCon -> TC m a -> TC m a
withoutConstructors tc = TC . M.R.local clean . unTC where
  -- Note: only filters immediate scope -- should be right.
  clean (TCEnv env) = TCEnv (map eachScope env)
  eachScope      :: Scope -> Scope 
  eachScope scope = genModify scope emptyPath flevel
  flevel         :: Level -> Level
  flevel level    = level { vlevel = eachVe (vlevel level) }
  eachVe         :: VE -> VE
  eachVe          = fromList . filter keep . toList
  keep           :: (BIdent R, Type) -> Bool
  keep (Con _, TyFun _ _ (TyApp tc' _ _)) = tc' /= tc
  keep (Con _, TyApp tc' _ _)             = tc' /= tc
  keep _                                  = True
-}

-- | Try to look up any environment binding (value, tycon, ...)
find :: (Monad m, GenLookup Context k v, Show k) =>
          k -> TC m v
find k = asksM $ \cxt -> case cxt =..= k of
  Just v  -> return v
  Nothing -> fail $
    "BUG! type checker got unbound identifier: " ++ show k

-- | Try to look up any environment binding (value, tycon, ...)
tryFind :: (Monad m, GenLookup Context k v, Show k) =>
          k -> TC m (Maybe v)
tryFind k = asks (=..= k)

---
--- Type errors
---

-- | Raise a type error, with the dynamically-bound source location
terr :: (?loc :: Loc, Monad m) => String -> m a
terr  = fail . (label ++)
  where label = if isBogus ?loc
                  then "type error: "
                  else show ?loc ++ ":\ntype error: "

-- | A type checking "assertion" raises a type error if the
--   asserted condition is false.
tassert :: (?loc :: Loc, Monad m) =>
           Bool -> String -> m ()
tassert True  _ = return ()
tassert False s = terr s

-- | A common form of type error: A got B where C expected
tgot :: (?loc :: Loc, Monad m) =>
        String -> Type -> String -> m a
tgot who got expected = terr $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- | Combination of 'tassert' and 'tgot'
tassgot :: (?loc :: Loc, Monad m) =>
           Bool -> String -> Type -> String -> m ()
tassgot False = tgot
tassgot True  = \_ _ _ -> return ()

-- | Run a partial computation, and if it fails, substitute
--   the given failure message for the one generated
(|!) :: (?loc :: Loc, Monad m) => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> terr s
infix 1 |!

-- | Conveniently weak-head normalize a type
hnT :: Monad m => Type -> m Type
hnT  = headNormalizeTypeM 100

-- | Check type for closed-ness and and defined-ness, and add info
tcType :: (?loc :: Loc, Monad m) =>
          Syntax.Type R -> TC m Type
tcType = tc where
  tc :: Monad m => Syntax.Type R -> TC m Type
  tc [$ty| '$tv |] = do
    return (TyVar tv)
  tc [$ty| $t1 -[$q]> $t2 |] = do
    TyFun <$> qInterpretM q
          <*> tcType t1
          <*> tcType t2
  tc [$ty| ($list:ts) $qlid:n |] = do
    ts'  <- mapM tc ts
    tc'  <- find n
    checkLength (length (tcArity tc'))
    checkBound (tcBounds tc') ts'
    return (tyApp tc' ts')
    where
      checkLength len =
        tassert (length ts == len) $
          "Type constructor " ++ show n ++ " applied to " ++
          show (length ts) ++ " arguments where " ++
          show len ++ " expected"
      checkBound quals ts' =
        tassert (all2 (\qlit t -> qualConst t <: qlit) quals ts') $
          "Type constructor " ++ show n ++
          " used at " ++ show (map (qRepresent . qualifier) ts') ++
          " where at most " ++ show quals ++ " is permitted"
  tc [$ty| $quant:u '$tv . $t |] =
    TyQu u tv <$> tc t
  tc [$ty| mu '$tv . $t |] = do
    case unfoldTyMu t of
      (_, N _ (Syntax.TyVar tv')) | tv == tv' ->
        terr $ "Recursive type ‘" ++ show (Syntax.tyMu tv t) ++
               "’ is not contractive."
      _ -> return ()
    t' <- tc t
    tassert (qualConst t' == tvqual tv) $
      "Recursive type " ++ show (Syntax.tyMu tv t) ++ " qualifier " ++
      "does not match its own type variable."
    return (TyMu tv t')
  tc [$ty| $anti:a |] = $antifail

-- | Type check an A expression
tcExpr :: Monad m => Expr R -> TC m (Type, Expr R)
tcExpr = tc where
  tc :: Monad m => Expr R -> TC m (Type, Expr R)
  tc e0 = let ?loc = getLoc e0 in case e0 of
    [$ex| $id:x |] -> do
      tx    <- find x
      x'    <- case view x of
                 Left _   -> return x
                 Right qu -> return (fmap Con qu)
      return (tx, [$ex|+ $id:x' |])
    [$ex| $str:s |] -> return (tyString, [$ex|+ $str:s |])
    [$ex| $int:z |] -> return (tyInt,    [$ex|+ $int:z |])
    [$ex| $flo:f |] -> return (tyFloat,  [$ex|+ $flo:f |])
    [$ex| match $e with $list:clauses |] -> do
      (t0, e') <- tc e
      (t1:ts, clauses') <- liftM unzip . forM clauses $ \(N note ca) -> do
        (xi', md) <- steal $ tcPatt t0 (capatt ca)
        (ti, ei') <- inModule md $ tc (caexpr ca)
        checkSharing "match" (caexpr ca) md
        return (ti, caClause xi' ei' <<@ note)
      tr <- foldM (\ti' ti -> ti' \/? ti
                      |! "Mismatch in match/let: " ++ show ti ++
                          " and " ++ show ti')
            t1 ts
      return (tr, [$ex|+ match $e' with $list:clauses' |])
    [$ex| let rec $list:bsN in $e2 |] -> do
      let bs = map dataOf bsN
      (tfs, md) <- steal $ forM bs $ \b -> do
        t' <- tcType (bntype b)
        tassert (syntacticValue (bnexpr b)) $
          "Not a syntactic value in let rec: " ++ show (bnexpr b)
        tassert (qualConst t' <: Qu) $
          "Affine type in let rec binding: " ++ show t'
        bindVar (bnvar b) t'
        return t'
      (tas, e's) <- liftM unzip $ inModule md $ mapM (tc . bnexpr) bs
      zipWithM_ (\tf ta ->
                   tassert (ta <: tf) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- inModule md $ tc e2
      let b's =
            zipWith3
              (\b tf e' -> newBinding b { bntype = typeToStx tf, bnexpr = e' })
              bs tfs e's
      return (t2, [$ex|+ let rec $list:b's in $e2' |])
    [$ex| let $decl:d in $e2 |] -> do
      (d', md)  <- steal $ tcDecl d
      (t2, e2') <- inModule md $ tc e2
      return (t2, [$ex|+ let $decl:d' in $e2' |])
    [$ex| ($e1, $e2) |] -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return (t1 .*. t2, [$ex|+ ($e1', $e2') |])
    [$ex| fun ($x : $t) -> $e |] -> do
      t' <- tcType t
      (x', md) <- steal $ tcPatt t' x
      checkSharing "lambda" e md
      (te, e') <- inModule md $ tc e
      q <- getWorthiness e0
      return (TyFun q t' te, [$ex|+ fun ($x' : $stx:t') -> $e' |])
    [$ex| $_ $_ |] -> do
      tcExApp tc e0
    [$ex| fun '$tv -> $e |] -> do
      tassert (syntacticValue e) $
        "Not a syntactic value under type abstraction: " ++ show e0
      (t, e') <- tc e
      return (tyAll tv t, [$ex|+ fun '$tv -> $e' |])
    [$ex| $e1 [$t2] |] -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      t1'       <- tapply t1 t2'
      return (t1', [$ex|+ $e1' [$stx:t2'] |])
    [$ex| Pack[$opt:mt1]($t2, $e) |] -> do
      t2'      <- tcType t2
      (te, e') <- tc e
      t1'      <- case mt1 of
        Just t1 -> tcType t1
        Nothing -> return (makeExType te t2')
      case t1' of
        TyQu Exists tv t11' -> do
          te' <- tapply (tyAll tv t11') t2'
          tassert (te <: te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1'
          return (t1', [$ex| Pack[$stx:t1']($stx:t2', $e') |])
        _ -> tgot "Pack[-]" t1' "ex(istential) type"
    [$ex| ( $e1 : $t2 ) |] -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      tassgot (t1 <: t2')
        "type ascription (:)" t1 (show t2')
      return (t2', e1')
    [$ex| ( $e1 :> $t2 ) |] -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      tassgot (castableType t2')
        "cast (:>)" t1 "function type"
      e1'' <- coerceExpression (e1' <<@ e0) t1 t2'
      -- tcExpr e1'' -- re-type check the coerced expression
      return (t2', e1'')
    [$ex| $anti:a |]    -> $antifail
    [$ex| $antiL:a |]   -> $antifail
  --
  -- | Assert that type given to a name is allowed by its usage
  checkSharing :: (Monad m, ?loc :: Loc) =>
                  String -> Expr R -> Module -> TC m ()
  checkSharing name e = loop where
    loop md0 = case md0 of
      MdApp md1 md2     -> do loop md1; loop md2
      MdValue (Var l) t ->
          tassert (qualConst t <: usage (J [] l) e) $
            "Affine variable " ++ show l ++ " : " ++
            show t ++ " duplicated in " ++ name ++ " body"
      _                 -> return ()
  --
  -- | What is the join of the qualifiers of all free variables
  --   of the given expression?
  getWorthiness e =
    liftM bigVee . forM (M.keys (fv e)) $ \x -> do
      mtx <- tryFind (fmap Var x)
      return $ case mtx of
        Just tx -> qualifier tx
        _       -> minBound

-- | Remove all instances of t2 from t1, replacing with
--   a new type variable 
makeExType :: Type -> Type -> Type
makeExType t1 t2 = TyQu Exists tv $ everywhere (mkT erase) t1 where
  tv       = fastFreshTyVar (TV (lid "a") (qualConst t2)) (maxtv (t1, t2))
  erase t' = if t' == t2 then TyVar tv else t'

-- Get the usage (sharing) of a variable in an expression:
usage :: QLid R -> Expr R -> QLit
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- | Type check an application, given the type subsumption
--   relation, the appropriate type checking function, and the
--   expression to check.
--
-- This is highly ad-hoc, as it does significant local type inference.
-- Ick.
tcExApp :: (?loc :: Loc, Monad m) =>
           (Expr R -> TC m (Type, Expr R)) ->
           Expr R -> TC m (Type, Expr R)
tcExApp tc e0 = do
  let foralls t1 ts = do
        let (tvs, t1f) = vtQus Forall t1 -- peel off quantification
            (tas, _)   = vtFuns t1f      -- peel off arg types
            nargs      = min (length tas) (length ts)
            tup ps     = foldl tyTuple tyUnit (take nargs ps)
        -- try to find types to unify formals and actuals, and apply
        t1' <- tryUnify tvs (tup tas) (tup ts) >>= foldM tapply t1
        arrows t1' ts
      arrows tr                   [] = return tr
      arrows t'@(view -> TyQu Forall _ _) ts = foralls t' ts
      arrows (view -> TyFun _ ta tr) (t:ts) = do
        b <- unifies [] t ta
        tassgot b "Application (operand)" t (show ta)
        arrows tr ts
      arrows (view -> TyMu tv t') ts = arrows (tysubst tv (TyMu tv t') t') ts
      arrows t' _ = tgot "Application (operator)" t' "function type"
      unifies tvs ta tf =
        case tryUnify tvs ta tf of
          Just ts  -> do
            ta' <- foldM tapply (foldr tyAll ta tvs) ts
            if (ta' <: tf)
              then return True
              else deeper
          Nothing -> deeper
        where
          deeper = case ta of
            TyQu Forall tv ta1 -> unifies (tvs++[tv]) ta1 tf
            _                  -> return False
  let (es, e1) = unfoldExApp e0            -- get operator and args
  (t1, e1')   <- tc e1                     -- check operator
  (ts, es')   <- unzip `liftM` mapM tc es  -- check args
  tr <- foralls t1 ts
  return (tr, foldl exApp e1' es')

-- | Figure out the result type of a type application, given
--   the type of the function and the argument type
tapply :: (?loc :: Loc, Monad m) =>
          Type -> Type -> m Type
tapply (view -> TyQu Forall tv t1') t2 = do
  tassert (qualConst t2 <: tvqual tv) $
    "Type application cannot instantiate type variable " ++
    show tv ++ " with type " ++ show t2
  return (tysubst tv t2 t1')
tapply t1 _ = tgot "type application" t1 "(for)all type"

-- Given the type of thing to match and a pattern, return
-- the type environment bound by that pattern.
tcPatt :: (?loc :: Loc, Monad m) =>
          Type -> Patt R -> TC m (Patt R)
tcPatt t x0 = case x0 of
  [$pa| _ |]      -> return x0
  [$pa| $lid:x |] -> x0 <$ bindVar x t
  [$pa| $quid:u $opt:mx |] -> do
    t' <- hnT t
    case t' of
      TyApp _ ts _ -> do
        tu <- find (fmap Con u)
        (params, mt, res) <- case vtQus Forall tu of
          (params, TyFun _ arg res)
            -> return (params, Just arg, res)
          (params, res)
            -> return (params, Nothing, res)
        tassgot (t' <: tysubsts params ts res)
          "Pattern" t' ("constructor " ++ show u)
        case (mt, mx) of
          (Nothing, Nothing) ->
            return [$pa|+ $quid:u |]
          (Just t1, Just x1) -> do
            let t1' = tysubsts params ts t1
            x1' <- tcPatt t1' x1
            return [$pa|+ $quid:u $x1' |]
          _ -> tgot "Pattern" t "wrong arity"
      _ | isBotType t' -> case mx of
            Nothing -> return x0
            Just x  -> tcPatt tyBot x
        | otherwise -> tgot "Pattern" t' ("constructor " ++ show u)
  [$pa| ($x, $y) |] -> do
    t' <- hnT t >>! mapBottom (tyApp tcTuple . replicate 2)
    case t' of
      TyApp tc [xt, yt] _ | tc == tcTuple -> do
        x' <- tcPatt xt x
        y' <- tcPatt yt y
        return [$pa| ($x', $y') |]
      _ -> tgot "Pattern " t' "pair type"
  [$pa| $str:_ |] -> do
      tassgot (t <: tyString)
        "Pattern" t "string"
      return x0
  [$pa| $int:_ |] -> do
      tassgot (t <: tyInt)
        "Pattern" t "int"
      return x0
  [$pa| $flo:_ |] -> do
      tassgot (t <: tyFloat)
        "Pattern" t "float"
      return x0
  [$pa| $x as $lid:y |] -> do
    x' <- tcPatt t x
    bindVar y t
    return [$pa| $x' as $lid:y |]
  [$pa| Pack('$tv, $x) |] -> do
    t' <- hnT t >>! mapBottom (tyEx tv)
    case t' of
      TyQu Exists tve te -> do
        tassert (tvqual tve <: tvqual tv) $
          "Cannot bind existential tyvar " ++ show tv ++
          " to " ++ show tve
        let te' = tysubst tve (TyVar tv) te
        x' <- tcPatt te' x
        return [$pa| Pack('$tv, $x') |]
      _ -> tgot "Pattern" t' "existential type"
  [$pa| $antiL:a |] -> $antifail
  [$pa| $anti:a |]  -> $antifail

-- | Check if type is bottom, and if so, apply the given function
--   to it
mapBottom :: (Type -> Type) -> Type -> Type
mapBottom ft t
  | isBotType t = ft t
  | otherwise   = t

-- Given a list of type variables tvs, a type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (?loc :: Loc, Monad m) =>
            [TyVarR] -> Type -> Type -> m [Type]
tryUnify [] _ _        = return []
tryUnify tvs t t'      = 
  case subtype 100 [] t' tvs t of
    Left s         -> giveUp (s :: String)
    Right (_, ts)  -> return ts
  where
  giveUp _ = terr $
    "\nCannot guess type" ++
    (if length tvs == 1 then " t1" else "s t1, .., t" ++ show (length tvs))
    ++ " such that\n  " ++ showsPrec 10 t "" ++
    concat [ "[t" ++ show i ++ "/" ++ show tv ++ "]"
           | tv <- tvs | i <- [ 1.. ] :: [Integer] ] ++
    "\n  >: " ++ show t'

-- | Convert qualset representations from a list of all tyvars and
--   list of qualifier-significant tyvars to a set of type parameter
--   indices
indexQuals :: (?loc :: Loc, Monad m) =>
              Lid R -> [TyVarR] -> QExp R -> TC m (QDen Int)
indexQuals name tvs qexp = do
  qden <- qInterpretM qexp
  numberQDenM unbound tvs qden where
  unbound tv = terr $ "unbound tyvar " ++ show tv ++
                      " in qualifier list for type " ++ show name

-- BEGIN type decl checking

-- | Run a computation in the context of type declarations
tcTyDecs :: (?loc :: Loc, Monad m) =>
            [TyDec R] -> TC m [TyDec R]
tcTyDecs tds0 = do
  let (atds, stds, dtds) = foldr partition ([], [], []) tds0
  -- stds <- topSort getEdge stds0
  (_, stub) <- steal $ forM (atds ++ dtds ++ stds) $ \td0 ->
    case dataOf td0 of
      TdDat name params _   -> allocStub name (map tvqual params)
      TdSyn name ((ps,_):_) -> allocStub name (map (const Qa) ps)
      TdAbs name params variances quals -> do
        quals' <- indexQuals name params quals
        ix     <- newIndex
        us     <- currentModulePath
        let tc' = mkTC ix (J us name) quals'
                       [ (tvqual parm, var)
                       | var <- variances
                       | parm <- params ]
        bindTycon name tc'
      _                     -> return ()
  let loop md = do
        ((changed, tcs), md') <-
          steal $
            inModule md $
              liftM unzip $
                mapM tcTyDec (atds ++ dtds ++ stds)
        if or changed
          then loop md'
          else return (tcs, md')
   in do
     (tcs, md') <- loop stub
     forM_ tcs $ \tc -> do
       case tcNext tc of
         Nothing      -> return ()
         Just clauses -> forM_ clauses $ \(tps, rhs) ->
           tassert (rhs /= tyPatToType (TpApp tc {tcNext = Nothing} tps)) $
             "Type synonym ‘" ++ show tc ++ "’ is not contractive."
     tell (replaceTyCons tcs md')
     return tds0
  where
    allocStub name params = do
      ix <- newIndex
      us <- currentModulePath
      let tc = mkTC ix (J us name)
                    [ (q, Omnivariant) | q <- params ]
      bindTycon name tc
    --
    getEdge td0 = case dataOf td0 of
      TdSyn name cs     -> (name, S.unions (map (tyConsOfType . snd) cs))
      TdAbs name _ _ _  -> (name, S.empty)
      TdDat name _ alts -> (name, names) where
        names = S.unions [ tyConsOfType t | (_, Just t) <- alts ]
      TdAnti a          -> $antierror
    --
    partition td (atds, stds, dtds) =
      case dataOf td of
        TdAbs _ _ _ _ -> (td : atds, stds, dtds)
        TdSyn _ _     -> (atds, td : stds, dtds)
        TdDat _ _ _   -> (atds, stds, td : dtds)
        TdAnti a      -> $antierror

-- tcTyDec types a type declaration, but in addition to
-- returnng a declaration, it returns a boolean that indicates
-- whether the type metadata has changed, which allows for iterating
-- to a fixpoint.
tcTyDec :: (?loc :: Loc, Monad m) =>
           TyDec R -> TC m (Bool, TyCon)
tcTyDec td0 = case dataOf td0 of
  TdAbs name _ _ _ -> do
    tc   <- find (J [] name :: QLid R)
    bindTycon name tc
    return (False, tc)
  TdSyn name cs -> do
    tc   <- find (J [] name :: QLid R)
    let nparams = length (fst (head cs))
    tassert (all ((==) nparams . length . fst) cs) $
      "all type operator clauses have the same number of parameters"
    (cs', quals, vqs) <- liftM unzip3 $ forM cs $ \(tps, rhs) -> do
      rhs' <- tcType rhs
      let vs1 = ftvVs rhs'
      (tps', tvses, vqs) <- liftM unzip3 $ forM tps $ \tp -> do
        tp' <- tcTyPat tp
        let tpt  = tyPatToType tp'
            vs2  = ftvVs tpt
            vs'  = M.intersectionWith (*) vs1 vs2
            var  = bigVee (M.elems vs')
            qp   = qualConst tpt
            tvs  = qDenFtv (qualifier tpt)
        return (tp', tvs, (var, qp))
      let tvmap = M.unions [ M.fromDistinctAscList
                               [ (tv, i) | tv <- S.toAscList tvs ]
                           | tvs <- tvses
                           | i <- [ 0 .. ] ]
          qual  = numberQDenMap tvqual tvmap (qualifier rhs')
      return ((tps', rhs'), qual, vqs)
    let (arity, bounds) = unzip (map bigVee (transpose vqs))
        qual    = bigVee quals
        changed = arity /= tcArity tc
               || qual  /= tcQual tc
        tc'     = tc { tcArity = arity,    tcQual = qual,
                       tcNext  = Just cs', tcBounds = bounds }
    bindTycon name tc'
    return (changed, tc')
  TdDat name params alts -> do
    tc <- find (J [] name :: QLid R)
    alts' <- sequence
      [ case mt of
          Nothing -> return (cons, Nothing)
          Just t  -> do
            t' <- tcType t
            return (cons, Just t')
      | (cons, mt) <- alts ]
    let t'      = foldl tyTuple tyUnit [ t | (_, Just t) <- alts' ]
        qual    = numberQDen params (qualifier t')
        arity   = typeVariances params t'
        changed = arity /= tcArity tc
               || qual  /= tcQual tc
        tc'     = tc { tcArity = arity, tcQual = qual,
                       tcCons = (params, fromList alts') }
    bindTycon name tc'
    bindAlts params tc' alts'
    return (changed, tc')
  TdAnti a -> $antifail

-- | Build a module of datacon types from a datatype's
--   alternatives
bindAlts :: Monad m => [TyVarR] -> TyCon -> [(Uid R, Maybe Type)] -> TC m ()
bindAlts params tc = mapM_ each where
  each (u, Nothing) = bindCon u (alls result)
  each (u, Just t)  = bindCon u (alls (t .->. result))
  alls t            = foldr tyAll t params
  result            = tyApp tc (map TyVar params)

-- | Compute the variances at which some type variables occur
--   in an open type expression
typeVariances :: [TyVarR] -> Type -> [Variance]
typeVariances d0 = finish . ftvVs where
  finish m = [ maybe 0 id (M.lookup tv m)
             | tv <- d0 ]

-- | Generic topological sort
--
-- Uses an adjacency-list graph representation.  Given a
-- function from abstract node values to comparable nodes,
-- and a list of node values, returns a list of node values (or
-- fails if there's a cycle).
topSort :: forall node m a.
           (?loc :: Loc, Monad m, Ord node, Show node) =>
           (a -> (node, S.Set node)) -> [a] -> m [a]
topSort getEdge edges = do
  (_, w) <- RWS.execRWST visitAll S.empty S.empty
  return w
  where
    visitAll = mapM_ visit (M.keys graph)
    --
    visit :: node -> RWS.RWST (S.Set node) [a] (S.Set node) m ()
    visit node = do
      stack <- RWS.ask
      tassert (not (node `S.member` stack)) $
        "unproductive cycle in type definitions, via type " ++ show node
      seen <- RWS.get
      if node `S.member` seen
        then return ()
        else do
          RWS.put (S.insert node seen)
          case M.lookup node graph of
            Just (succs, info) -> do
              RWS.local (S.insert node) $
                mapM_ visit succs
              RWS.tell [info]
            Nothing ->
              return ()
    --
    graph :: M.Map node ([node], a)
    graph = M.fromList [ let (node, succs) = getEdge info
                          in (node, (S.toList succs, info))
                       | info <- edges ]

-- | The (unqualified) tycons that appear in a syntactic type
tyConsOfType :: Syntax.Type R -> S.Set (Lid R)
tyConsOfType [$ty| ($list:ts) $qlid:n |] =
  case n of
    J [] l -> S.singleton l
    _      -> S.empty
  `S.union` S.unions (map tyConsOfType ts)
tyConsOfType [$ty| '$_ |]              = S.empty
tyConsOfType [$ty| $t1 -[$_]> $t2 |]   =
  tyConsOfType t1 `S.union` tyConsOfType t2
tyConsOfType [$ty| $quant:_ '$_. $t |] = tyConsOfType t
tyConsOfType [$ty| mu '$_. $t |]       = tyConsOfType t
tyConsOfType [$ty| $anti:a |]          = $antierror

tcTyPat :: Monad m => Syntax.TyPat R -> TC m TyPat
tcTyPat (N note (Syntax.TpVar tv var))    = do
  let ?loc = getLoc note
  tassert (var == Invariant) $
    "type pattern variable " ++ show tv ++
    " cannot have a variance annotation"
  return (TpVar tv)
tcTyPat tp@[$tpQ| ($list:tps) $qlid:qu |] = do
  let ?loc = _loc
  tc <- find qu
  tassert (isNothing (tcNext tc)) $
    "type operator pattern `" ++ show tp ++
    "' cannot also be a type operator"
  TpApp tc <$> mapM tcTyPat tps
tcTyPat [$tpQ| $antiP:a |]             = $antifail

-- END type decl checking

-- | Type check a module body
tcSigExp :: (?loc :: Loc, Monad m) =>
            SigExp R -> TC m (SigExp R)
tcSigExp [$seQ| sig $list:ds end |] = do
  ds' <- tcMapM tcSigItem ds
  return [$seQ| sig $list:ds' end |]
tcSigExp [$seQ| $quid:n $list:qls |] = do
  (md, _) <- find (fmap SIGVAR n)
  tell md
  return [$seQ| $quid:n $list:qls |]
tcSigExp [$seQ| $se1 with type $list:tvs $qlid:tc = $t |] = do
  (se1', md) <- steal $ tcSigExp se1
  t'         <- tcType t
  fibrate tvs tc t' md
  return [$seQ| $se1' with type $list:tvs $qlid:tc = $t |]
tcSigExp [$seQ| $anti:a |] = $antifail

fibrate :: (?loc :: Loc, Monad m) =>
           [TyVar R] -> QLid R -> Type -> Module -> TC m ()
fibrate tvs ql t md = do
    let Just tc = findTycon ql md
    tassert (isAbstractTyCon tc) $
      "with-type: cannot update concrete type constructor `" ++
      show ql
    tassert (length tvs == length (tcArity tc)) $
      "with-type: " ++ show (length tvs) ++
      " parameters for type " ++ show ql ++
      " which has " ++ show (length (tcArity tc))
    let amap   = ftvVs t
        arity  = map (\tv -> fromJust (M.lookup tv amap)) tvs
        bounds = map tvqual tvs
        qual   = numberQDen tvs (qualifier t)
        next   = Just [(map TpVar tvs, t)]
        tc'    = tc {
                   tcArity  = arity,
                   tcBounds = bounds,
                   tcQual   = qual,
                   tcNext   = next
                 }
    tell (replaceTyCon tc' md)
  where
    findTycon ql0 md0 = case md0 of
      MdNil          -> mzero
      MdApp md1 md2  -> findTycon ql0 md1 `mplus` findTycon ql0 md2
      MdTycon l tc   -> if J [] l == ql0 then return tc else mzero
      MdModule u md1 -> case ql0 of
        J (u':us) l | u == u' -> findTycon (J us l) md1
        _                     -> mzero
      MdSig _ _      -> mzero
      MdValue _ _    -> mzero

tcSigItem :: (?loc :: Loc, Monad m) =>
             SigItem R -> TC m (SigItem R)
tcSigItem sg0 = case sg0 of
  [$sgQ| val $lid:l : $t |] -> do
    t' <- tcType t
    bindVar l t'
    return [$sgQ| val $lid:l : $t |]
  [$sgQ| type $list:tds |] -> do
     tds' <- tcTyDecs tds
     return [$sgQ| type $list:tds' |]
  [$sgQ| module $uid:u : $se1 |] -> do
    (se', md) <- steal $ tcSigExp se1
    bindModule u md
    return [$sgQ| module $uid:u : $se' |]
  [$sgQ| module type $uid:u = $se1 |] -> do
    se' <- tcSig u se1
    return [$sgQ| module type $uid:u = $se' |]
  [$sgQ| include $se1 |] -> do
    se' <- tcSigExp se1
    return [$sgQ| include $se' |]
  [$sgQ| exception $uid:u of $opt:mt |] -> do
    mt' <- tcException u mt
    return [$sgQ| exception $uid:u of $opt:mt' |]
  [$sgQ| $anti:a |] -> $antifail

-- | Run a computation in the context of a let declaration
tcLet :: (?loc :: Loc, Monad m) =>
         Patt R -> Maybe (Syntax.Type R) -> Expr R ->
         TC m (Patt R, Maybe (Syntax.Type R), Expr R)
tcLet x mt e = do
  tassert (S.null (dtv x)) $
    "Cannot unpack existential in top-level binding"
  (te, e') <- tcExpr e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (qualConst t' == Qu) $
        "Declared type of top-level binding " ++ show x ++ " is not unlimited"
      tassert (te <: t') $
        "Declared type for top-level binding " ++ show x ++ " : " ++ show t' ++
        " is not subsumed by actual type " ++ show te
      return t'
    Nothing -> do
      tassert (qualConst te == Qu) $
        "Type of top-level binding `" ++ show x ++ "' is not unlimited"
      return te
  x' <- tcPatt t' x
  return (x', Just (typeToStx t'), e')

-- | Run a computation in the context of a module open declaration
tcOpen :: (?loc :: Loc, Monad m) =>
          ModExp R -> TC m (ModExp R)
tcOpen b = tcModExp b

-- | Run a computation in the context of a local block (that is, after
--   the block)
tcLocal :: (?loc :: Loc, Monad m) =>
           [Decl R] -> [Decl R] ->
           TC m ([Decl R], [Decl R])
tcLocal ds1 ds2 = do
  (ds1', md1) <- steal $ tcDecls ds1
  ds2' <- inModule md1 $ tcDecls ds2
  return (ds1', ds2')

-- | Run a computation in the context of a new exception variant
tcException :: (?loc :: Loc, Monad m) =>
               Uid R -> Maybe (Syntax.Type R) ->
               TC m (Maybe (Syntax.Type R))
tcException n mt = do
  mt' <- gmapM tcType mt
  bindCon n (maybe tyExn (`tyArr` tyExn) mt')
  return (fmap typeToStx mt')

-- | Type check and bind a module
tcMod :: (?loc :: Loc, Monad m) =>
         Uid R -> ModExp R -> TC m (ModExp R)
tcMod u me0 = do
  (me', md) <- steal $ enterModule u $ tcModExp me0
  bindModule u md
  return me'

-- | Type check and bind a signature
tcSig :: (?loc :: Loc, Monad m) =>
         Uid R -> SigExp R -> TC m (SigExp R)
tcSig u se0 = do
  (se', md) <- steal $ tcSigExp se0
  bindSig u md
  return se'

{-
-- | Determine types that are no longer reachable by name
--   in a given scope, and give them an ugly printing name
hideInvisible :: Monad m =>
                 Scope -> TC m Scope
hideInvisible (PEnv modenv level) = do
  level' <- withAny level $ everywhereM (mkM repair) level
  withAny level' $ do
    ((), modenv') <- mapAccumM
                   (\scope acc -> do
                      scope' <- hideInvisible scope
                      return (acc, scope'))
                   () modenv
    return (PEnv modenv' level')
  where
    repair :: Monad m => Type -> TC m Type
    repair t@(TyApp tc ts cache) = do
      mtc <- tryGetAny (tcName tc)
      return $ if mtc == Just tc
        then t
        else TyApp (hide tc) ts cache
    repair t = return t
    --
    hide :: TyCon -> TyCon
    hide tc@TyCon { tcName = J (Uid _ "?" : _) _ } = tc
    hide tc@TyCon { tcName = J qs (Lid _ k), tcId = i } =
      tc { tcName = J (Uid "?":qs) (Lid _ (k ++ ':' : show i)) }

-- | Replace the printing name of each type with the shortest
--   path to access that type.  (So unnecessary!)
requalifyTypes :: [Uid R] -> E -> E
requalifyTypes _uids env = map (fmap repairLevel) env where
  repairLevel :: Level -> Level
  repairLevel level = everywhere (mkT repair) level
  --
  repair :: TypeT -> TypeT
  repair t@(TyCon { }) = case tyConsInThisEnv -.- ttId (tyinfo t) of
    Nothing   -> t
    Just name -> t `setTycon` name
  repair t = t
  --
  tyConsInThisEnv :: Env Integer (QLid R)
  tyConsInThisEnv  = uids <...> foldr addToScopeMap empty env
  --
  addToScopeMap :: Scope -> Env Integer (QLid R) -> Env Integer (QLid R)
  addToScopeMap (PEnv ms level) acc = 
    foldr (Env.unionWith chooseQLid) acc
      (makeLevelMap level :
       [ uid <..> addToScopeMap menv empty
       | (uid, menv) <- toList ms ])
  --
  makeLevelMap (Level _ ts) =
    fromList [ (ttId tag, J [] lid)
             | (lid, info) <- toList ts,
               tag <- tagOfTyInfo info ]
  --
  tagOfTyInfo (TiAbs tag)     = [tag]
  tagOfTyInfo (TiSyn _ _)     = []
  tagOfTyInfo (TiDat tag _ _) = [tag]
  tagOfTyInfo TiExn           = [tdExn]
  --
  chooseQLid :: QLid R -> QLid R -> QLid R
  chooseQLid q1@(J p1 _) q2@(J p2 _)
    | length p1 < length p2 = q1
    | otherwise             = q2
  --
  (<..>) :: Functor f => p -> f (Path p k) -> f (Path p k)
  (<..>)  = fmap . (<.>)
  --
  (<...>) :: Functor f => [p] -> f (Path p k) -> f (Path p k)
  (<...>) = flip $ foldr (<..>)
-}

-- | Type check a module body
tcModExp :: (?loc :: Loc, Monad m) =>
            ModExp R -> TC m (ModExp R)
tcModExp [$me| struct $list:ds end |] = do
  ds' <- tcDecls ds
  return [$me| struct $list:ds' end |]
tcModExp [$me| $quid:n $list:qls |] = do
  (md, _) <- find n
  tell md
  return [$me| $quid:n $list:qls |]
tcModExp [$me| $me1 : $se2 |] = do
  (me1', md1) <- steal $ tcModExp me1
  (se2', md2) <- steal $ tcSigExp se2
  ascribeSignature md1 md2
  return [$me| $me1' : $se2' |]
tcModExp [$me| $anti:a |] = $antifail

-- | Run a computation in the context of an abstype block
tcAbsTy :: (?loc :: Loc, Monad m) =>
            [AbsTy R] -> [Decl R] ->
            TC m ([AbsTy R], [Decl R])
tcAbsTy atds ds = do
  (_,   md1) <- steal $ tcTyDecs (map (atdecl . dataOf) atds)
  (ds', md2) <- steal $ inModule md1 $ tcDecls ds
  tcs <- forM atds $ \at0 -> case view at0 of
    AbsTy arity quals (N _ (TdDat name params _)) -> do
      let env = envify md1
          tc  = fromJust (env =..= name)
      qualSet <- indexQuals name params quals
      tassert (length params == length (tcArity tc)) $
        "abstract-with-end: " ++ show (length params) ++
        " given for type " ++ show name ++
        " which has " ++ show (length (tcArity tc))
      tassert (all2 (<:) (tcArity tc) arity) $
        "abstract-with-end: declared arity for type " ++ show name ++
        ", " ++ show arity ++
        ", is more general than actual arity " ++ show (tcArity tc)
      tassert (tcQual tc <: qualSet) $ 
        "abstract-with-end: declared qualifier for type " ++ show name ++
        ", " ++ show qualSet ++
        ", is more general than actual qualifier " ++ show (tcQual tc)
      return $ abstractTyCon tc {
        tcQual  = qualSet,
        tcArity = arity,
        tcCons  = ([], empty)
      }
    _ -> terr "(BUG) Can't abstract non-datatypes"
  tell (replaceTyCons tcs (md1 `mappend` md2))
  return (atds, ds')

-- | Type check a declaration
tcDecl :: Monad m => Decl R -> TC m (Decl R)
tcDecl decl =
  let ?loc = getLoc decl in
    case decl of
      [$dc| let $x : $opt:t = $e |] -> do
        (x', t', e') <- tcLet x t e
        return [$dc| let $x' : $opt:t' = $e' |] 
      [$dc| type $list:tds |] -> do
        tds' <- tcTyDecs tds
        return [$dc| type $list:tds' |]
      [$dc| abstype $list:at with $list:ds end |] -> do
        (at', ds') <- tcAbsTy at ds
        return [$dc| abstype $list:at' with $list:ds' end |]
      [$dc| module $uid:x = $b |] -> do
        b' <- tcMod x b
        return [$dc| module $uid:x = $b' |]
      [$dc| module type $uid:x = $b |] -> do
        b' <- tcSig x b
        return [$dc| module type $uid:x = $b' |]
      [$dc| open $b |] -> do
        b' <- tcOpen b
        return [$dc| open $b' |]
      [$dc| local $list:ds0 with $list:ds1 end |] -> do
        (ds0', ds1') <- tcLocal ds0 ds1
        return [$dc| local $list:ds0' with $list:ds1' end |]
      [$dc| exception $uid:n of $opt:mt |] -> do
        mt' <- tcException n mt
        return [$dc| exception $uid:n of $opt:mt' |]
      [$dc| $anti:a |] -> $antifail

-- | Type check a sequence of declarations
tcDecls :: Monad m => [Decl R] -> TC m [Decl R]
tcDecls = tcMapM tcDecl

---
--- Module sealing
---

-- | For mapping renamed names (from structures) into unrenamed names
--   (in signatures)
data NameMap
  = NameMap {
      nmValues  :: Env (BIdent R) (BIdent R),
      nmTycons  :: Env (Lid R)    (Lid R),
      nmModules :: Env (Uid R)    (Uid R, NameMap),
      nmSigs    :: Env (Uid R)    (Uid R)
  }

instance Monoid NameMap where
  mempty = NameMap empty empty empty empty
  mappend (NameMap a1 a2 a3 a4) (NameMap b1 b2 b3 b4) =
    NameMap (a1 =+= b1) (a2 =+= b2) (a3 =+= b3) (a4 =+= b4) where

instance GenEmpty NameMap where
  genEmpty = mempty
instance GenExtend NameMap NameMap where
  (=+=) = mappend
instance GenLookup NameMap (BIdent R) (BIdent R) where
  e =..= k = nmValues e =..= k
instance GenLookup NameMap (Lid R) (Lid R) where
  e =..= k = nmTycons e =..= k
instance GenLookup NameMap (Uid R) (Uid R, NameMap) where
  e =..= k = nmModules e =..= k
instance GenLookup NameMap SIGVAR (Uid R) where
  e =..= k = nmSigs e =..= unSIGVAR k

-- | Given a module, construct a 'NameMap' mapping raw versions of its
--   names to the actual renamed version.
makeNameMap :: Module -> NameMap
makeNameMap md0 = case md0 of
  MdNil          -> mempty
  MdApp md1 md2  -> makeNameMap md1 =+= makeNameMap md2
  MdValue x _    -> mempty { nmValues  = unnameBIdent x =:= x }
  MdTycon x _    -> mempty { nmTycons  = unnameLid x =:= x }
  MdModule x md1 -> mempty { nmModules = unnameUid x =:= (x, makeNameMap md1) }
  MdSig x _      -> mempty { nmSigs    = unnameUid x =:= x }
  where
    unnameLid :: Lid R -> Lid R
    unnameLid  = lid . unLid
    unnameUid :: Uid R -> Uid R
    unnameUid  = uid . unUid
    unnameBIdent :: BIdent R -> BIdent R
    unnameBIdent (Var l) = Var (unnameLid l)
    unnameBIdent (Con u) = Con (unnameUid u)

-- | Given a module and a signature, ascribe the signature to the module
--   and write the result.
ascribeSignature :: (?loc :: Loc, Monad m) =>
                    Module -> Module -> TC m ()
ascribeSignature md1 md2 = do
  let md2'   = renameSig (makeNameMap md1) md2
  onlyInModule md1 $ do
    subst <- matchSigTycons md2'
    subsumeSig (applyTyConSubstInSig subst md2')
  let tcs    = getGenTycons md2' []
  tcs'      <- forM tcs $ \tc -> do
    ix <- newIndex
    return tc { tcId = ix }
  tell (substTyCons tcs tcs' md2')

-- | Make the names in a signature match the names from the module it's
--   being applied to.
renameSig :: NameMap -> Module -> Module
renameSig nm0 = loop where
  loop md0 = case md0 of
    MdNil          -> MdNil
    MdApp md1 md2  -> MdApp (loop md1) (loop md2)
    MdValue x t    -> MdValue (fromJust (nm0 =..= x)) t
    MdTycon x tc   -> MdTycon (fromJust (nm0 =..= x)) tc
    MdModule x md1 ->
      let Just (x', nm1) = nm0 =..= x
       in MdModule x' (renameSig nm1 md1)
    MdSig x md1    -> MdSig (fromJust (nm0 =..= SIGVAR x)) md1

-- | Given a signature, find the tycon substitutions necessary to
--   unify it with the module in the environment.
matchSigTycons :: Monad m => Module -> TC m TyConSubst
matchSigTycons = loop [] where
  loop path md0 = case md0 of
    MdNil          -> return mempty
    MdApp md1 md2  -> mappend <$> loop path md1 <*> loop path md2
    MdValue _ _    -> return mempty
    MdTycon x tc   -> do
      tc' <- find (J path x)
      return (makeTyConSubst [tc] [tc'])
    MdModule x md1 -> loop (path++[x]) md1
    MdSig _ _      -> return mempty

-- | Given a tycon substitution, apply it to all the values and
--   RIGHT-HAND-SIDES of type definitions in a signature.  In
--   particular, don't replace any tycon bindings directly, but do
--   replace any references to other types in their definitions.
applyTyConSubstInSig :: TyConSubst -> Module -> Module
applyTyConSubstInSig subst = loop where
  loop md0   = case md0 of
    MdNil          -> MdNil
    MdApp md1 md2  -> MdApp (loop md1) (loop md2)
    MdValue x t    -> MdValue x (applyTyConSubst subst t)
    MdTycon x tc   -> MdTycon x (applyTyConSubstInTyCon subst tc)
    MdModule x md1 -> MdModule x (loop md1)
    MdSig x md1    -> MdSig x (loop md1)

-- | Get a list of all the tycons that need a new index allocated
--   because they're generative.
getGenTycons :: Module -> [TyCon] -> [TyCon]
getGenTycons = loop where
  loop MdNil            = id
  loop (MdApp md1 md2)  = loop md1 . loop md2
  loop (MdValue _ _)    = id
  loop (MdTycon _ tc)   = if varietyOf tc == OperatorType
                            then id
                            else (tc:)
  loop (MdModule _ md1) = loop md1
  loop (MdSig _ _)      = id

-- | Check whether the given signature subsumes the signature
--   implicit in the environment; takes a 'NameMap' mapping un-renamed
--   signature names to renamed environment names.
subsumeSig :: (?loc :: Loc, Monad m) =>
              Module -> TC m ()
subsumeSig = loop where
  loop md0 = case md0 of
    MdNil         -> return ()
    MdApp md1 md2 -> do loop md1; loop md2
    MdValue x t    -> do
      t' <- find (J [] x :: Ident R)
      tassgot (t' <: t)
        ("in signature matching, variable `"++show x++"'") t' (show t)
    MdTycon x tc   -> do
      tc' <- find (J [] x :: QLid R)
      case varietyOf tc of
        AbstractType -> do
          tassert (length (tcArity tc') == length (tcArity tc)) $
            "in signature matching, cannot match type definition for " ++
            show (tcName tc) ++ " because the actual number of type " ++
            "parameters (" ++ show (length (tcArity tc')) ++
            " does not match the expected number (" ++
            show (length (tcArity tc)) ++ "("
          tassert (all2 (<:) (tcArity tc') (tcArity tc)) $
            "in signature matching, cannot match type definition for " ++
            show (tcName tc) ++ " because actual variance " ++
            show (tcArity tc') ++
            " is less general than expected variance " ++
            show (tcArity tc)
          tassert (all2 (<:) (tcBounds tc') (tcBounds tc)) $
            "in signature matching, cannot match type definition for " ++
            show (tcName tc) ++ " because actual parameter bounds " ++
            show (tcBounds tc') ++
            " is less general than expected parameter bounds " ++
            show (tcBounds tc)
          tassert (tcQual tc' <: tcQual tc) $ 
            "in signature matching, cannot match type definition for " ++
            show (tcName tc) ++ " because actual qualifier " ++
            show (tcQual tc') ++
            " is less general than expected qualifier " ++
            show (tcQual tc)
        OperatorType -> matchTycons tc' tc
        DataType     -> matchTycons tc' tc
    MdModule x md1 -> do
      (md2, _) <- find (J [] x :: QUid R)
      onlyInModule md2 $ subsumeSig md1
    MdSig x md1    -> do
      (md2, _)  <- find (J [] (SIGVAR x) :: Path (Uid R) SIGVAR)
      matchSigs md2 md1

-- | Check that two signatures match EXACTLY.
matchSigs :: (?loc :: Loc, Monad m) =>
             Module -> Module -> TC m ()
matchSigs md10 md20 = loop (linearize md10 []) (linearize md20 []) where
  loop [] []                = return ()
  loop (MdValue x1 t1 : sgs1) (MdValue x2 t2 : sgs2)
    | x1 == x2 && t1 == t2  = loop sgs1 sgs2
  loop (MdTycon x1 tc1 : sgs1) (MdTycon x2 tc2 : sgs2)
    | x1 == x2              = do
      matchTycons tc1 tc2
      loop (substTyCon tc1 tc2 sgs1) sgs2
  loop (MdModule x1 md1 : sgs1) (MdModule x2 md2 : sgs2)
    | x1 == x2              = do
      matchSigs md1 md2
      loop sgs1 sgs2
  loop (MdSig x1 md1 : sgs1) (MdSig x2 md2 : sgs2)
    | x1 == x2              = do
      matchSigs md1 md2
      loop sgs1 sgs2
  loop [] (sg : _)          = do
    terr $ "cannot match signature item: " ++ name sg
  loop (sg : _) []          = do
    terr $ "cannot match signature item: " ++ name sg
  loop (sg1 : _) (sg2 : _)  = do
    terr $ "cannot match signature items: " ++ name sg1 ++
           " and " ++ name sg2
  --
  name (MdValue x _)  = "value " ++ show x
  name (MdTycon x _)  = "type " ++ show x
  name (MdModule x _) = "module " ++ show x
  name (MdSig x _)    = "module type " ++ show x
  name _              = error "BUG! in Statics.matchSigs"

-- | Extensional equality for type constructors
tyconExtEq :: TyCon -> TyCon -> Bool
tyconExtEq tc1 tc2 | tcBounds tc1 == tcBounds tc2 =
  let tvs = zipWith (TyVar .) tvalphabet (tcBounds tc1)
   in tyApp tc1 tvs == tyApp tc2 tvs
tyconExtEq _   _   = False

-- | Check that two type constructors match exactly.
matchTycons :: (?loc :: Loc, Monad m) =>
               TyCon -> TyCon -> TC m ()
matchTycons tc1 tc2 = case (varietyOf tc1, varietyOf tc2) of
  (AbstractType, AbstractType) -> do
    tassert (tcArity tc1 == tcArity tc2) $
      estr "the arity" (show (tcArity tc1)) (show (tcArity tc2))
    tassert (tcBounds tc1 == tcBounds tc2) $
      estr "parameter bounds" (show (tcBounds tc1)) (show (tcBounds tc2))
    tassert (tcQual tc1 == tcQual tc2) $
      estr "qualifier" (show (tcQual tc1)) (show (tcQual tc2))
  (DataType, DataType) -> do
    let (tvs1, rhs1) = tcCons tc1
        (tvs2, rhs2) = tcCons tc2
    tassert (length tvs1 == length tvs2) $
      estr "number of parameters" (show (length tvs1)) (show (length tvs2))
    let mtv   = maxtv (tvs1, tvs2, Env.range rhs1, Env.range rhs2)
        tvs'  = fastFreshTyVars tvs1 mtv
        rhs1' = Env.mapVals (fmap (tysubsts tvs1 (map TyVar tvs'))) rhs1
        rhs2' = Env.mapVals (fmap (tysubsts tvs2 (map TyVar tvs'))) rhs2
    forM_ (Env.toList rhs1') $ \(k, t1) ->
      let Just t2 = rhs2' =..= k
       in tassert (t1 == t2) $ estr
            ("constructor `" ++ show k ++ "'")
            (maybe "nothing" show t1)
            (maybe "nothing" show t2)
  (OperatorType, _)            | tyconExtEq tc1 tc2 -> return ()
  (_,            OperatorType) | tyconExtEq tc1 tc2 -> return ()
  (OperatorType, OperatorType) -> do
    let next1 = fromJust (tcNext tc1)
        next2 = fromJust (tcNext tc2)
    tassert (length next1 == length next2) $
      estr "number of clauses" (show (length next1)) (show (length next2))
    forM_ (zip3 next1 next2 [1 :: Int .. ]) $
      \((tp1, t1), (tp2, t2), ix) -> do
        tassert (length tp1 == length tp2) $
          estr ("number of parameters in clause " ++ show ix)
               (show (length tp1)) (show (length tp2))
        (tvs1, tvs2) <- mconcat `liftM` zipWithM matchTypats tp1 tp2
        let mtv   = maxtv (tvs1, tvs2, t1, t2)
            tvs'  = fastFreshTyVars tvs1 mtv
            t1'   = tysubsts tvs1 (map TyVar tvs') t1
            t2'   = tysubsts tvs2 (map TyVar tvs') t2
        tassert (t1' == t2') $
          estr ("type operator right-hand sides in clause " ++ show ix)
               (show t1') (show t2')
  (v1, v2) -> terr $ estr "kind of definition" (show v1) (show v2)
  where
    estr what which1 which2 =
      "in signature matching, cannot match type definition for " ++
      show (tcName tc1) ++ " because the " ++ what ++
      " does not match (`" ++ which1 ++ "' vs. `" ++ which2 ++ "')"

-- | Check that two type patterns match, and return the pairs of
--   type variables that line up and thus need renaming.
matchTypats :: (?loc :: Loc, Monad m) =>
               TyPat -> TyPat -> TC m ([TyVar R], [TyVar R])
matchTypats (TpVar tv1) (TpVar tv2)
  = return ([tv1], [tv2])
matchTypats (TpApp tc1 tvs1) (TpApp tc2 tvs2)
  | tc1 == tc2
  = mconcat `liftM` zipWithM matchTypats tvs1 tvs2
matchTypats tp1 tp2
  = terr $ "in signature matching, cannot match type patterns `" ++
           show tp1 ++ "' and `" ++ show tp2 ++ "'"

-- | To flatten all the 'MdNil' and 'MdApp' constructors in a module
--   into an ordinary list.
linearize :: Module -> [Module] -> [Module]
linearize MdNil           = id
linearize (MdApp md1 md2) = linearize md1 . linearize md2
linearize md1             = (md1 :)

---
--- END Module Sealing
---

-- | Add the type of a value binding
addVal :: Monad m => Lid R -> Syntax.Type R -> TC m ()
addVal x t = do
  let ?loc = mkBogus "<addVal>"
  t' <- tcType t
  bindVar x t'

-- | Add an arbitrary declaration
addDecl     :: Monad m => Decl R -> TC m ()
addDecl d    = () <$ tcDecl d

-- | Add a type constructor binding
addType     :: Monad m => Lid R -> TyCon -> TC m ()
addType n tc = () <$ bindTycon n tc

-- | Add a nested submodule
addMod :: Monad m => Uid R -> TC m a -> TC m ()
addMod u action = do
  (_, md) <- steal $ enterModule u $ action
  bindModule u md

-- | Type check a program
tcProg :: Monad m => Prog R -> TC m (Type, Prog R)
tcProg [$prQ| $list:ds in $opt:e0 |] = do
  (ds', md) <- steal $ tcDecls ds
  (t, e0')  <- case e0 of
    Just e  -> liftM (second Just) $ inModule md $ tcExpr e
    Nothing -> return (tyUnit, Nothing)
  return (t, [$prQ|+ $list:ds' in $opt:e0' |])

-- | The initial type-checking state
env0 :: S
env0  = S e0 0 where
  e0 :: E
  e0  = genEmpty =+= (Con (uid "()") -:- tyUnit :: VE)

-- | Find out the parameter type of an exception
getExnParam :: Type -> Maybe (Maybe Type)
getExnParam (TyApp tc _ _)
  | tc == tcExn             = Just Nothing
getExnParam (TyFun _ t1 (TyApp tc _ _))
  | tc == tcExn             = Just (Just t1)
getExnParam _               = Nothing

-- | Reconstruct the declaration from a tycon binding, for printing
tyConToDec :: TyCon -> TyDec R
tyConToDec tc = case tc of
  _ | tc == tcExn
    -> tdAbs (lid "exn") [] [] maxBound
  TyCon { tcName = n, tcNext = Just clauses }
    -> tdSyn (jname n) [ (map tyPatToStx ps, typeToStx rhs)
                       | (ps, rhs) <- clauses ]
  TyCon { tcName = n, tcCons = (ps, alts) }
    | not (isEmpty alts)
    -> tdDat (jname n) ps [ (u, fmap typeToStx mt)
                          | (u, mt) <- toList alts ]
  TyCon { tcName = n }
    ->
    let tyvars = zipWith ($) tvalphabet (tcBounds tc)
     in tdAbs (jname n)
              (zipWith const tyvars (tcArity tc))
              (tcArity tc)
              (qRepresent
                (denumberQDen
                  (map (qInterpret . qeVar) tyvars)
                  (tcQual tc)))

getVarInfo :: QLid R -> S -> Maybe Type
getVarInfo ql (S e _) = e =..= fmap Var ql

getTypeInfo :: QLid R -> S -> Maybe TyCon
getTypeInfo ql (S e _) = e =..= ql

-- Find out about a type constructor.  If it's an exception constructor,
-- return 'Left' with its paramter, otherwise return the type construtor
-- of the result type
getConInfo :: QUid R -> S -> Maybe (Either (Maybe Type) TyCon)
getConInfo qu (S e _) = do
  t <- e =..= fmap Con qu
  case getExnParam t of
    Just mt -> Just (Left mt)
    Nothing ->
      let loop (TyFun _ _ t2) = loop t2
          loop (TyQu _ _ t1)  = loop t1
          loop (TyApp tc _ _) = Just (Right tc)
          loop _              = Nothing
       in loop t

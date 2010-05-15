-- | The type checker
{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleContexts,
      FlexibleInstances,
      ImplicitParams,
      MultiParamTypeClasses,
      ParallelListComp,
      QuasiQuotes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances,
      ViewPatterns #-}
module Statics (
  -- * Static environments
  S, env0,
  -- ** Environment construction
  addVal, addType, addExn, addMod,
  -- * Type checking
  tcProg, tcDecls,
  -- ** Type checking results for the REPL
  NewDefs(..), V, T, emptyNewDefs, TyCon, tyConToDec
) where

import Meta.Quasi
import Util
import qualified Syntax
import qualified Syntax.Notable
import qualified Syntax.Expr
import qualified Syntax.Decl
import Syntax hiding (Type, Type'(..), tyAll, tyEx, tyUn, tyAf,
                      tyTuple, tyUnit, tyArr, tyApp)
import Loc
import Env as Env
import Ppr ()
import Type
import TypeRel
import Coercion (coerceExpression)

import Data.Data (Typeable, Data)
import Data.Generics (everywhere, mkT{-, everywhereM, mkM-})
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Control.Monad.Reader as M.R
import qualified Control.Monad.State  as M.S
import qualified Control.Monad.RWS    as RWS

import System.IO.Unsafe (unsafePerformIO)
p :: Show a => a -> b -> b
p a b = unsafePerformIO (print a) `seq` b
pM :: (Show a, Monad m) => a -> m ()
pM a = if p a True then return () else fail "wibble"
-- p = const

-- Get the usage (sharing) of a variable in an expression:
usage :: QLid -> Expr i -> QLit
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type environments
type D = Env TyVar TyVar       -- tyvars in scope, with idempot. renaming

-- | Mapping from identifiers to value types (includes datacons)
type V       = Env BIdent Type
-- | Mapping from type constructor names to tycon info
type T       = Env Lid TyCon
data Level   = Level {
                 vlevel :: V, -- values
                 tlevel :: T  -- types
               }
  deriving (Typeable, Data)
-- path env includes modules
type Scope = PEnv Uid Level
type E = [Scope]

emptyPath :: [Uid]
emptyPath  = []

-- Instances for generalizing environment operations over
-- the whole environment structure

instance GenEmpty Level where
  genEmpty = Level empty empty

instance GenExtend Level Level where
  Level ve te =+= Level ve' te' = Level (ve =+= ve') (te =+= te')
instance GenExtend Level V where
  level =+= ve' = level =+= Level ve' empty
instance GenExtend Level T where
  level =+= te' = level =+= Level empty te'
instance GenLookup Level BIdent Type where
  level =..= k = vlevel level =..= k
instance GenLookup Level Lid TyCon where
  level =..= k = tlevel level =..= k

-- | The packaged-up state of the type-checker, which needs to be
--   threaded from one interaction to the next by the REPL
data S   = S {
             -- | The environment, from language C's perspective
             cEnv    :: E,
             -- | Index for gensyms
             currIx  :: Integer
           }

-- | The type checking monad is the composition of
--   reader carrying an environment and state carrying a gensym counter,
--   parametric in the underlying monad.
newtype TC m a =
  TC { unTC :: M.R.ReaderT TCEnv (M.S.StateT Integer m) a }
-- | The environment contains type mappings and type variable
--   environments.
data TCEnv = TCEnv E D

instance GenLookup TCEnv QUid Scope where
  TCEnv env _ =..= k = env =..= k
instance GenLookup TCEnv QLid TyCon where
  TCEnv env _ =..= k = env =..= k
instance GenLookup TCEnv Ident Type where
  TCEnv env _ =..= k = env =..= k
instance GenLookup TCEnv TyVar TyVar where
  TCEnv _ d =..= k = d =..= k

instance GenExtend TCEnv Scope where
  TCEnv env dd =+= scope = TCEnv (env =+= scope) dd
instance GenExtend TCEnv Level where
  TCEnv env dd =+= level = TCEnv (env =+= level) dd
instance GenExtend TCEnv (Env Ident Type) where
  TCEnv env dd =+= venv = TCEnv (env =+= venv) dd
instance GenExtend TCEnv (Env Uid Scope) where
  TCEnv env dd =+= menv = TCEnv (env =+= menv) dd
instance GenExtend TCEnv T where
  TCEnv env dd =+= tenv = TCEnv (env =+= tenv) dd
instance GenExtend TCEnv V where
  TCEnv env dd =+= venv = TCEnv (env =+= venv) dd
instance GenExtend TCEnv D where
  TCEnv env d =+= tvs  = TCEnv env (d =+= tvs)

instance Monad m => Monad (TC m) where
  m >>= k = TC (unTC m >>= unTC . k)
  return  = TC . return
  fail    = TC . fail

instance Monad m => Functor (TC m) where
  fmap = liftM

instance Monad m => Applicative (TC m) where
  pure  = return
  (<*>) = ap

asksM :: M.R.MonadReader r m => (r -> m a) -> m a
asksM  = (M.R.ask >>=)

-- | Pack up the type-checking state as an 'S', to give to the REPL.
saveTC :: Monad m => Bool -> TC m S
saveTC interactive = do
  TCEnv env _ <- TC M.R.ask
  index       <- TC M.S.get
  let env' = if interactive
               then requalifyTypes [] env
               else env
  return S {
    cEnv   = env',
    currIx = index
  }

runTC :: Monad m => S -> TC m a -> m a
runTC s (TC m) = do
  let tc = TCEnv (cEnv s) empty
      ix = currIx s
  M.S.evalStateT (M.R.runReaderT m tc) ix

-- | Gensym
newIndex :: Monad m => TC m Integer
newIndex  = TC $ do
  M.S.modify (+ 1)
  M.S.get

-- | Run a computation with some type variables added to the
-- type variable environment
withTVs :: Monad m => [TyVar] -> ([TyVar] -> TC m a) -> TC m a
withTVs tvs m = TC $ do
  TCEnv env d <- M.R.ask
  let (d', tvs') = foldr rename (d, []) tvs
      r'         = TCEnv env d'
  M.R.local (const r') (unTC (m tvs'))
    where
      rename :: TyVar -> (D, [TyVar]) -> (D, [TyVar])
      rename tv (d, tvs') =
        let tv' = case d =..= tv of
                    Nothing -> tv
                    Just _  -> tv `freshTyVar` M.keysSet (unEnv d)
        in (d =+= tv =:+= tv', tv':tvs')

-- | Run a computation with some extension to the environment
withAny :: (Monad m, GenExtend TCEnv e') =>
           e' -> TC m a -> TC m a
withAny e' = TC . M.R.local (=+= e') . unTC

-- | Run a computation with the environment extended by some value
--   bindings
withVars :: Monad m => V -> TC m a -> TC m a
withVars  = withAny

-- | Run a computation with the environment extended by some tycon
--   bindings
withTypes :: Monad m => T -> TC m a -> TC m a
withTypes = withAny

-- | Run a computation with an additional, empty scope (which can then
--   be captures as a module)
pushScope :: Monad m => TC m a -> TC m a
pushScope = TC . M.R.local push . unTC where
  push (TCEnv env dd) = TCEnv (genEmpty : env) dd

-- | Collapse the top two scopes (as in opening a module or leaving a
--   local block)
squishScope :: Monad m => TC m a -> TC m a
squishScope = TC . M.R.local squish . unTC where
  squish (TCEnv (e0:e1:es) dd) = TCEnv ((e1=+=e0):es) dd
  squish (TCEnv env        dd) = TCEnv env dd

-- | Get the top scope
askScope :: Monad m => TC m Scope
askScope  = do
  TCEnv env _ <- TC M.R.ask
  case env of
    scope:_ -> return scope
    []      -> return genEmpty

-- | Abstract the given type by removing its datacon or synonym info
withoutConstructors :: Monad m =>
                       TyCon -> TC m a -> TC m a
withoutConstructors tc = TC . M.R.local clean . unTC where
  -- Note: only filters immediate scope -- should be right.
  clean (TCEnv env dd) = TCEnv (map eachScope env) dd
  eachScope      :: Scope -> Scope 
  eachScope scope = genModify scope emptyPath flevel
  flevel         :: Level -> Level
  flevel level    = level { vlevel = eachVe (vlevel level) }
  eachVe         :: V -> V
  eachVe          = fromList . filter keep . toList
  keep           :: (BIdent, Type) -> Bool
  keep (Con _, TyFun _ _ (TyApp tc' _ _)) = tc' /= tc
  keep (Con _, TyApp tc' _ _)             = tc' /= tc
  keep _                                  = True

-- | Repalce the type tag for the given type with the given
--   type tag while running a computation
withReplacedTyCons :: Monad m =>
                      TyCon -> TC m a -> TC m a
withReplacedTyCons tc = TC . M.R.local reptc . unTC
  where
    reptc (TCEnv env dd) = TCEnv (map (fmap replevel) env) dd
    replevel a = replaceTyCon tc a

-- | Try to look up any environment binding (value, tycon, ...)
tryGetAny :: (Monad m, GenLookup TCEnv k v, Show k) =>
             k -> TC m (Maybe v)
tryGetAny k = TC $ asksM (return . (=..= k))

-- | Look up any environment binding (value, tycon, ...), or fail
getAny :: (?loc :: Loc, Monad m, GenLookup TCEnv k v, Show k) =>
          String -> k -> TC m v
getAny msg k = do
  t <- tryGetAny k
  t |! msg ++ ": " ++ show k

-- | Make sure the given tyvar is in scope
getTV :: (?loc :: Loc, Monad m) => TyVar -> TC m TyVar
getTV  = getAny "Free type variable"

-- | Get the type of a variable, or fail
getVar :: (?loc :: Loc, Monad m) =>
          Ident -> TC m Type
getVar x = do
  t <- tryGetVar x
  t |! "Unbound variable: " ++ show x

-- | Try getting the type of a variable
tryGetVar :: Monad m =>
             Ident -> TC m (Maybe Type)
tryGetVar x = TC $ asksM (return . (=..= x))

-- | Get the info associated with a tycon, or fail
getType :: (?loc :: Loc, Monad m) => QLid -> TC m TyCon
getType  = getAny "Unbound type constructor"

-- | Look up a module, or fail
getModule :: (?loc :: Loc, Monad m) => QUid -> TC m Scope
getModule  = getAny "Unbound module identifier"

-- | Raise a type error, with the dynamically-bound source location
terr :: (?loc :: Loc, Monad m) => String -> m a
terr  = fail . (label ++)
  where label = "Type error: " ++ if isBogus ?loc
                                    then ""
                                    else show ?loc ++ ": "

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

hnT :: Monad m => Type -> m Type
hnT  = headNormalizeTypeM 100

-- | Check type for closed-ness and and defined-ness, and add info
tcType :: (?loc :: Loc, Monad m) =>
          Syntax.Type i -> TC m Type
tcType = tc where
  tc :: Monad m => Syntax.Type i -> TC m Type
  tc [$ty| '$tv |] = do
    TyVar <$> getTV tv
  tc [$ty| $t1 -[$q]> $t2 |] = do
    TyFun <$> qInterpretM q
          <*> tcType t1
          <*> tcType t2
  tc [$ty| ($list:ts) $qlid:n |] = do
    ts'  <- mapM tc ts
    tc'  <- getType n
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
    withTVs [tv] $ \[tv'] -> TyQu u tv' <$> tc t
  -- XXX need to handle mu 'a. forall 'b. ... 'a ... case
  tc [$ty| mu '$tv . $t |] = withTVs [tv] $ \[tv'] -> do
    t' <- tc t
    tassert (qualConst t' == tvqual tv) $
      "Recursive type " ++ show (Syntax.tyMu tv t) ++ " qualifier " ++
      "does not match its own type variable."
    return (TyMu tv' t')
  tc [$ty| $anti:a |] = $antifail

-- | Remove all instances of t2 from t1, replacing with
--   a new type variable 
makeExType :: Type -> Type -> Type
makeExType t1 t2 = TyQu Exists tv $ everywhere (mkT erase) t1 where
  tv       = freshTyVar (TV (Lid "a") (qualConst t2)) (ftv [t1, t2])
  erase t' = if t' == t2 then TyVar tv else t'

-- | Type check an A expression
tcExpr :: (Monad m, Id i) => Expr i -> TC m (Type, Expr i)
tcExpr = tc where
  tc :: (Monad m, Id i) => Expr i -> TC m (Type, Expr i)
  tc e0 = let ?loc = getLoc e0 in case e0 of
    [$ex| $id:x |] -> do
      tx    <- getVar x
      let e' = [$ex|+ $id:x |] `setExn` findIsExn tx
      return (tx, e')
    [$ex| $str:s |] -> return (tyString, [$ex|+ $str:s |])
    [$ex| $int:z |] -> return (tyInt,    [$ex|+ $int:z |])
    [$ex| $flo:f |] -> return (tyFloat,  [$ex|+ $flo:f |])
    [$ex| $antiL:a |] -> $antifail
    [$ex| match $e with $list:clauses |] -> do
      (t0, e') <- tc e
      (t1:ts, clauses') <- liftM unzip . forM clauses $ \(N _ ca) -> do
        (gi, xi', ti, ei') <- withPatt t0 (capatt ca) $ tc (caexpr ca)
        checkSharing "match" gi (caexpr ca)
        return (ti, caClause xi' ei')
      tr <- foldM (\ti' ti -> ti' \/? ti
                      |! "Mismatch in match/let: " ++ show ti ++
                          " and " ++ show ti')
            t1 ts
      return (tr, [$ex|+ match $e' with $list:clauses' |])
    [$ex| let rec $list:bsN in $e2 |] -> do
      let bs = map dataOf bsN
      tfs <- mapM (tcType . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            tassert (qualConst t <: Qu) $
              "Affine type in let rec binding: " ++ show t
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= bnvar b =:= t)
          makeG _    _       _       = return empty
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (withVars g' . tc . bnexpr) bs
      zipWithM_ (\tf ta ->
                   tassert (ta <: tf) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- withVars g' $ tc e2
      let b's =
            zipWith3
              (\b tf e' -> newBinding b { bntype = typeToStx tf, bnexpr = e' })
              bs tfs e's
      return (t2, [$ex|+ let rec $list:b's in $e2' |])
    [$ex| let $decl:d in $e2 |] ->
      withDecl d $ \d' -> do
        (t2, e2') <- tc e2
        return (t2, [$ex|+ let $decl:d' in $e2' |])
    [$ex| ($e1, $e2) |] -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return (t1 .*. t2, [$ex|+ ($e1', $e2') |])
    [$ex| fun ($x : $t) -> $e |] -> do
      t' <- tcType t
      (gx, x', te, e') <- withPatt t' x $ tc e
      checkSharing "lambda" gx e
      q <- getWorthiness e0
      return (TyFun q t' te, [$ex|+ fun ($x' : $stx:t') -> $e' |])
    [$ex| $_ $_ |] -> do
      tcExApp tc e0
    [$ex| fun '$tv -> $e |] ->
      withTVs [tv] $ \[tv'] -> do
        tassert (syntacticValue e) $
          "Not a syntactic value under type abstraction: " ++ show e0
        (t, e') <- tc e
        return (tyAll tv' t, [$ex|+ fun '$tv' -> $e' |])
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
    [$ex| ( $e1 : $opt:mt :> $ta ) |] -> do
      (t1, e1') <- tc e1
      t'  <- maybe (return t1) tcType mt
      ta' <- tcType ta
      tassgot (castableType ta')
        "cast (:>)" t' "function type"
      tassgot (t1 <: t')
        "cast (:>)" t1 (show t')
      e1'' <- coerceExpression (e1' <<@ e0) t' ta'
      -- tcExpr e1'' -- re-type check the coerced expression
      return (ta', e1'')
    [$ex| $anti:a |] -> $antifail

  -- | Assert that type given to a name is allowed by its usage
  checkSharing :: (Monad m, ?loc :: Loc) =>
                  String -> V -> Expr i -> TC m ()
  checkSharing name g e =
    forM_ (toList g) $ \(x, tx) ->
      case x of
        Var x' ->
          tassert (qualConst tx <: usage (J [] x') e) $
            "Affine variable " ++ show x' ++ " : " ++
            show tx ++ " duplicated in " ++ name ++ " body"
        _ -> return ()

  -- | What is the join of the qualifiers of all free variables
  --   of the given expression?
  getWorthiness e =
    liftM bigVee . forM (M.keys (fv e)) $ \x -> do
      mtx <- tryGetVar (fmap Var x)
      return $ case mtx of
        Just tx -> qualifier tx
        _       -> minBound

-- | Type check an application, given the type subsumption
--   relation, the appropriate type checking function, and the
--   expression to check.
--
-- This is highly ad-hoc, as it does significant local type inference.
-- Ick.
tcExApp :: (?loc :: Loc, Monad m) =>
           (Expr i -> TC m (Type, Expr i)) ->
           Expr i -> TC m (Type, Expr i)
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
          Type -> Patt i -> TC m (D, V, Patt i)
tcPatt t x0 = case x0 of
  [$pa| _ |]      -> return (empty, empty, x0)
  [$pa| $lid:x |] -> return (empty, Var x =:= t, x0)
  N _ (PaCon u mx _) -> do
    t' <- hnT t
    case t' of
      TyApp _ ts _ -> do
        tu <- getVar (fmap Con u)
        (params, mt, res) <- case vtQus Forall tu of
          (params, TyFun _ arg res)
            -> return (params, Just arg, res)
          (params, res)
            -> return (params, Nothing, res)
        tassgot (t' <: tysubsts params ts res)
          "Pattern" t' ("constructor " ++ show u)
        let isexn = findIsExn t'
        case (mt, mx) of
          (Nothing, Nothing) ->
            return (empty, empty, paCon u Nothing isexn)
          (Just t1, Just x1) -> do
            let t1' = tysubsts params ts t1
            (dx1, gx1, x1') <- tcPatt t1' x1
            return (dx1, gx1, paCon u (Just x1') isexn)
          _ -> tgot "Pattern" t "wrong arity"
      _ | isBotType t' -> case mx of
            Nothing -> return (empty, empty, x0)
            Just x  -> tcPatt tyBot x
        | otherwise -> tgot "Pattern" t' ("constructor " ++ show u)
  [$pa| ($x, $y) |] -> do
    t' <- hnT t >>! mapBottom (tyApp tcTuple . replicate 2)
    case t' of
      TyApp tc [xt, yt] _ | tc == tcTuple -> do
        (dx, gx, x') <- tcPatt xt x
        (dy, gy, y') <- tcPatt yt y
        tassert (isEmpty (gx -|- gy)) $
          "Pattern " ++ show x0 ++ " binds variable twice"
        tassert (isEmpty (dx -|- dy)) $
          "Pattern " ++ show x0 ++ " binds type variable twice"
        return (dx =+= dy, gx =+= gy, [$pa| ($x', $y') |])
      _ -> tgot "Pattern " t' "pair type"
  [$pa| $str:s |] -> do
      tassgot (t <: tyString)
        "Pattern" t "string"
      return (empty, empty, [$pa| $str:s |])
  [$pa| $int:z |] -> do
      tassgot (t <: tyInt)
        "Pattern" t "int"
      return (empty, empty, [$pa| $int:z |])
  [$pa| $flo:f |] -> do
      tassgot (t <: tyFloat)
        "Pattern" t "float"
      return (empty, empty, [$pa| $flo:f |])
  [$pa| $antiL:a |] -> $antifail
  [$pa| $x as $lid:y |] -> do
    (dx, gx, x') <- tcPatt t x
    let gy        = y =:= t
    tassert (isEmpty (gx -|- gy)) $
      "Pattern " ++ show x0 ++ " binds " ++ show y ++ " twice"
    return (dx, gx =+= gy, [$pa| $x' as $lid:y |])
  [$pa| Pack('$tv, $x) |] -> do
    t' <- hnT t >>! mapBottom (tyEx tv)
    case t' of
      TyQu Exists tve te -> do
        tassert (tvqual tve <: tvqual tv) $
          "Cannot bind existential tyvar " ++ show tv ++
          " to " ++ show tve
        withTVs [tv] $ \[tv'] -> do
          let te' = tysubst tve (TyVar tv') te
          (dx, gx, x') <- tcPatt te' x
          tassert (dx =..= tv == Nothing) $
            "Pattern " ++ show x0 ++ " binds " ++ show tv ++ " twice"
          return (dx =+= tv =:+= tv', gx, [$pa| Pack('$tv', $x') |])
      _ -> tgot "Pattern" t' "existential type"
  [$pa| $anti:a |] -> $antifail

-- | Check if type is bottom, and if so, apply the given function
--   to it
mapBottom :: (Type -> Type) -> Type -> Type
mapBottom ft t
  | isBotType t = ft t
  | otherwise   = t

-- | Run a computation in the context of the bindings from
--   a pattern.
withPatt :: (?loc :: Loc, Monad m) =>
            Type -> Patt i -> TC m (Type, e) ->
            TC m (V, Patt i, Type, e)
withPatt t x m = do
  (d, g, x') <- tcPatt t x
  (t', e')   <- withAny d $ withVars g $ m
  -- tcType t'
  let escapees = S.fromList (range d) `S.intersection` ftv t'
  tassert (S.null escapees) $
    "Type variable escaped existential: " ++ show (S.findMin escapees)
  return (g, x', t', e')

-- Given a list of type variables tvs, a type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (?loc :: Loc, Monad m) =>
            [TyVar] -> Type -> Type -> m [Type]
tryUnify [] _ _        = return []
tryUnify tvs t t'      = 
  case subtype 100 [] t' tvs t of
    Left s         -> giveUp s
    Right (_, ts)  -> return ts
  where
  giveUp s = terr $
    "\nCannot guess type" ++
    (if length tvs == 1 then " t1" else "s t1, .., t" ++ show (length tvs))
    ++ " such that\n  " ++ showsPrec 10 t "" ++
    concat [ "[t" ++ show i ++ "/" ++ show tv ++ "]"
           | tv <- tvs | i <- [ 1.. ] :: [Integer] ] ++
    "\n  >: " ++ show t'
    ++ "\n(" ++ s ++ ")"

{- -- deprecated?
-- Given a type variable tv, type t in which tv may be free,
-- and a second type t', finds a plausible candidate to substitute
-- for tv to make t and t' unify.  (The answer it finds doesn't
-- have to be correct.
findSubst :: TyVar -> Type -> Type -> [Type]
findSubst tv = chk [] where
  chk, cmp :: [(AType, AType)] -> Type -> Type -> [Type]
  chk seen t1 t2 =
    let tw1 = AType t1; tw2 = AType t2
     in if (tw1, tw2) `elem` seen
          then []
          else cmp ((tw1, tw2) : seen) t1 t2

  cmp _    (TyVar tv') t'
    | tv == tv'    = [t']
  cmp seen [$ty|@! ($list:ts) $qlid:_ |] [$ty| ($list:ts') $qlid:_ |]
                   = concat (zipWith (chk seen) ts ts')
  cmp seen [$ty|@! $t1 -[$q]> $t2 |] [$ty| $t1' -[$q']> $t2' |]
                   = chkQe q q' ++ chk seen t1 t1' ++ chk seen t2 t2'
  cmp seen [$ty|@! $quant:_ '$tv0. $t |] [$ty| $quant:_ '$tv0'. $t' |]
    | tv /= tv0    = [ tr | tr <- chk seen t t',
                            not (tv0  `S.member` ftv tr),
                            not (tv0' `S.member` ftv tr) ]
  cmp seen [$ty| mu '$a. $t |] t'
                   = chk seen (tysubst a (TyMu a t) t) t'
  cmp seen t' [$ty| mu '$a. $t |]
                   = chk seen t' (tysubst a (TyMu a t) t)
  cmp _ _ _        = []

  chkQe :: QExp TyVar -> QExp TyVar -> [Type]
  chkQe (QeVar tv1) (QeVar tv2) | tv1 == tv = [TyVar tv2]
                                | tv2 == tv = [TyVar tv1]
  chkQe (QeVar tv1) (QeLit Qu)  | tv1 == tv = [tyUn]
  chkQe (QeLit Qu)  (QeVar tv2) | tv2 == tv = [tyUn]
  chkQe (QeVar tv1) (QeLit Qa)  | tv1 == tv = [tyAf]
  chkQe (QeLit Qa)  (QeVar tv2) | tv2 == tv = [tyAf]
  chkQe _           _                       = []
-}

-- | Convert qualset representations from a list of all tyvars and
--   list of qualifier-significant tyvars to a set of type parameter
--   indices
indexQuals :: (?loc :: Loc, Monad m) =>
              Lid -> [TyVar] -> QExp TyVar -> TC m (QDen Int)
indexQuals name tvs qexp = do
  qden <- qInterpretM qexp
  numberQDenM unbound tvs qden where
  unbound tv = terr $ "unbound tyvar " ++ show tv ++
                      " in qualifier list for type " ++ show name

-- BEGIN type decl checking

-- | Run a computation in the context of type declarations
withTyDecs :: (?loc :: Loc, Monad m) =>
              [TyDec i] -> ([TyDec i] -> TC m a) -> TC m a
withTyDecs tds0 k0 = do
  tassert (unique (map (tdaName . dataOf) tds0)) $
    "Duplicate type(s) in recursive type declaration"
  let (atds, stds0, dtds) = foldr partition ([], [], []) tds0
  stds <- topSort getEdge stds0
  mapCont_ withStub (dtds ++ stds) $
    let loop =
          mapCont withTyDec (atds ++ dtds ++ stds) $
            \tds'changed ->
              if any snd tds'changed
                then loop
                else k0 (map fst tds'changed)
     in loop
  where
    withStub td0 k = case dataOf td0 of
      TdDat name params _ -> allocStub name params k
      TdSyn name params _ -> allocStub name params k
      _                   -> k
    --
    allocStub name params k = do
      tassert (unique params) "Repeated type parameter"
      index <- newIndex
      let tc = mkTC index (unLid name)
                    [ (tvqual tv, Omnivariant) | tv <- params ]
      withTypes (name =:= tc) k
    --
    getEdge td0 = case dataOf td0 of
      TdSyn name _ t    -> (name, tyConsOfType t)
      TdAbs name _ _ _  -> (name, S.empty)
      TdDat name _ alts -> (name, names) where
        names = S.unions [ tyConsOfType t | (_, Just t) <- alts ]
      TdAnti a          -> $antierror
    --
    partition td (atds, stds, dtds) =
      case dataOf td of
        TdAbs _ _ _ _ -> (td : atds, stds, dtds)
        TdSyn _ _ _   -> (atds, td : stds, dtds)
        TdDat _ _ _   -> (atds, stds, td : dtds)
        TdAnti a      -> $antierror

-- withTyDec types a type declaration, but in addition to
-- return (in CPS) a declaration, it returns a boolean that indicates
-- whether the type metadata has changed, which allows for iterating
-- to a fixpoint.
withTyDec :: (?loc :: Loc, Monad m) =>
             TyDec i -> ((TyDec i, Bool) -> TC m a) -> TC m a
withTyDec td0 k = case dataOf td0 of
  TdAbs name params variances quals -> do
    tassert (unique params) "Repeated type parameter"
    index  <- newIndex
    quals' <- indexQuals name params quals
    withTypes
      (name =:= mkTC index (unLid name) quals'
                [ (tvqual parm, var) | var <- variances | parm <- params ])
      (k (tdAbs name params variances quals, False))
  TdSyn name params rhs -> do
    tc <- getType (J [] name)
    (params', rhs') <- withTVs params $ \params' -> do
      rhs' <- tcType rhs
      return (params', rhs')
    let qual    = numberQDen params' (qualifier rhs')
        arity   = typeVariances params' rhs'
        changed = arity /= tcArity tc
               || qual  /= tcQual tc
        tc'     = tc { tcArity = arity, tcQual = qual,
                       tcNext  = Just [(map TpVar params', rhs')] }
    withTypes (name =:= tc')
      (k (tdSyn name params rhs, changed))
  TdDat name params alts -> do
    tc <- getType (J [] name)
    (params', alts') <-
      withTVs params $ \params' -> do
        alts' <- sequence
          [ case mt of
              Nothing -> return (cons, Nothing)
              Just t  -> do
                t' <- tcType t
                return (cons, Just t')
          | (cons, mt) <- alts ]
        return (params', alts')
    let t'      = foldl tyTuple tyUnit [ t | (_, Just t) <- alts' ]
        qual    = numberQDen params' (qualifier t')
        arity   = typeVariances params' t'
        changed = arity /= tcArity tc
               || qual  /= tcQual tc
        tc'     = tc { tcArity = arity, tcQual = qual,
                       tcCons = (params', fromList alts') }
    withTypes (name =:= tc') $
      withVars (alts2env params' tc' alts') $
        (k (tdDat name params alts, changed))
  TdAnti a -> $antifail

-- | Are all elements of the list unique?
unique :: Ord a => [a] -> Bool
unique  = loop S.empty where
  loop _    []     = True
  loop seen (x:xs) = x `S.notMember` seen && loop (S.insert x seen) xs

-- | Build an environment of datacon types from a datatype's
--   alternatives
alts2env :: [TyVar] -> TyCon -> [(Uid, Maybe Type)] -> V
alts2env params tc = fromList . map each where
  each (uid, Nothing) = (Con uid, alls result)
  each (uid, Just t)  = (Con uid, alls (t .->. result))
  alls t              = foldr tyAll t params
  result              = tyApp tc (map TyVar params)

-- | Compute the variances at which some type variables occur
--   in an open type expression
typeVariances :: [TyVar] -> Type -> [Variance]
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

    graph :: M.Map node ([node], a)
    graph = M.fromList [ let (node, succs) = getEdge info
                          in (node, (S.toList succs, info))
                       | info <- edges ]

-- | The (unqualified) tycons that appear in a syntactic type
tyConsOfType :: Syntax.Type i -> S.Set Lid
tyConsOfType [$ty| ($list:ts) $qlid:n |] =
  case n of
    J [] lid -> S.singleton lid
    _        -> S.empty
  `S.union` S.unions (map tyConsOfType ts)
tyConsOfType [$ty| '$_ |]              = S.empty
tyConsOfType [$ty| $t1 -[$_]> $t2 |]   =
  tyConsOfType t1 `S.union` tyConsOfType t2
tyConsOfType [$ty| $quant:_ '$_. $t |] = tyConsOfType t
tyConsOfType [$ty| mu '$_. $t |]       = tyConsOfType t
tyConsOfType [$ty| $anti:a |]          = $antierror

-- END type decl checking

-- | Run a computation in the context of a let declaration
withLet :: (?loc :: Loc, Monad m, Id i) =>
           Patt i -> Maybe (Syntax.Type i) -> Expr i ->
           (Patt i -> Maybe (Syntax.Type i) -> Expr i -> TC m a) ->
           TC m a
withLet x mt e k = do
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
  (d, g, x') <- tcPatt t' x
  tassert (isEmpty d) $
    "Cannot unpack existential in top-level binding"
  withVars g $
    k x' (Just (typeToStx t')) e'

-- | Run a computation in the context of a module open declaration
withOpen :: (?loc :: Loc, Monad m, Id i) =>
            ModExp i -> (ModExp i -> TC m a) -> TC m a
withOpen b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [] [scope]
  withAny scope' $ k b'

-- | Run a computation in the context of a local block (that is, after
--   the block)
withLocal :: (?loc :: Loc, Monad m, Id i) =>
             [Decl i] -> [Decl i] ->
             ([Decl i] -> [Decl i] -> TC m a) -> TC m a
withLocal ds0 ds1 k = do
  (scope, ds0', ds1') <-
    pushScope $
      withDecls ds0 $ \ds0' ->
        pushScope $
          withDecls ds1 $ \ds1' -> do
            scope <- askScope
            return (scope, ds0', ds1')
  pushScope .
    withAny scope .
      squishScope $
        k ds0' ds1'

-- | Run a computation in the context of a new exception variant
withExn :: (?loc :: Loc, Monad m) =>
           Uid -> Maybe (Syntax.Type i) ->
           (Maybe (Syntax.Type i) -> TC m a) -> TC m a
withExn n mt k = do
  mt'   <- gmapM tcType mt
  withVars (Con n =:= maybe tyExn (`tyArr` tyExn) mt') $
    k (fmap typeToStx mt')

-- Is the given type the type of an exception constructor?
-- INVARIANT: The type must be weak head-normal.
findIsExn :: Type -> Bool
findIsExn (TyFun _ _ (TyApp tc _ _)) = tc == tcExn
findIsExn (TyApp tc _ _)             = tc == tcExn
findIsExn _ = False

-- | Run a computation in the context of a module
withMod :: (?loc :: Loc, Monad m, Id i) =>
           Uid -> ModExp i -> (ModExp i -> TC m a) -> TC m a
withMod x b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [x] [scope]
  withAny (x =:= scope') $ k b'

-- | Determine types that are no longer reachable by name
--   in a given scope, and give them an ugly printing name
hideInvisible :: Monad m =>
                 Scope -> TC m Scope
hideInvisible (PEnv modenv level) = return (PEnv modenv level) {- do
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
    hide tc@TyCon { tcName = J (Uid "?" : _) _ } = tc
    hide tc@TyCon { tcName = J qs (Lid k), tcId = i } =
      tc { tcName = J (Uid "?":qs) (Lid (k ++ ':' : show i)) }
-}

-- | Replace the printing name of each type with the shortest
--   path to access that type.  (So unnecessary!)
requalifyTypes :: [Uid] -> E -> E
requalifyTypes _uids env = env {- map (fmap repairLevel) env where
  repairLevel :: Level -> Level
  repairLevel level = everywhere (mkT repair) level

  repair :: TypeT -> TypeT
  repair t@(TyCon { }) = case tyConsInThisEnv -.- ttId (tyinfo t) of
    Nothing   -> t
    Just name -> t `setTycon` name
  repair t = t

  tyConsInThisEnv :: Env Integer QLid
  tyConsInThisEnv  = uids <...> foldr addToScopeMap empty env

  addToScopeMap :: Scope -> Env Integer QLid -> Env Integer QLid
  addToScopeMap (PEnv ms level) acc = 
    foldr (Env.unionWith chooseQLid) acc
      (makeLevelMap level :
       [ uid <..> addToScopeMap menv empty
       | (uid, menv) <- toList ms ])

  makeLevelMap (Level _ ts) =
    fromList [ (ttId tag, J [] lid)
             | (lid, info) <- toList ts,
               tag <- tagOfTyInfo info ]

  tagOfTyInfo (TiAbs tag)     = [tag]
  tagOfTyInfo (TiSyn _ _)     = []
  tagOfTyInfo (TiDat tag _ _) = [tag]
  tagOfTyInfo TiExn           = [tdExn]

  chooseQLid :: QLid -> QLid -> QLid
  chooseQLid q1@(J p1 _) q2@(J p2 _)
    | length p1 < length p2 = q1
    | otherwise             = q2

  (<..>) :: Functor f => p -> f (Path p k) -> f (Path p k)
  (<..>)  = fmap . (<.>)

  (<...>) :: Functor f => [p] -> f (Path p k) -> f (Path p k)
  (<...>) = flip $ foldr (<..>)

-}
-- | Type check a module body
tcModExp :: (?loc :: Loc, Monad m, Id i) =>
             ModExp i -> TC m (ModExp i, Scope)
tcModExp [$me| struct $list:ds end |] =
  pushScope $
    withDecls ds $ \ds' -> do
      scope <- askScope
      return ([$me| struct $list:ds' end |], scope)
tcModExp [$me| $quid:n $list:qls |] = do
  scope <- getModule n
  return ([$me| $quid:n $list:qls |], scope)
tcModExp [$me| $anti:a |] = $antifail

-- | Run a computation in the context of an abstype block
withAbsTy :: (?loc :: Loc, Monad m, Id i) =>
             [AbsTy i] -> [Decl i] ->
             ([AbsTy i] -> [Decl i] -> TC m a) ->
             TC m a
withAbsTy atds ds k0 =
  let atds' = map view atds
      vars  = map atvariance atds'
      quals = map atquals atds'
      tds   = map atdecl atds' in
  withTyDecs tds $ \tds' ->
    withDecls ds $ \ds' ->
      mapCont absDecl atds $ \tcs' ->
        k0 (zipWith3 absTy vars quals tds')
           (foldr replaceTyCon ds' tcs')
  where
    absDecl at0 k = case view at0 of
      AbsTy arity quals (N _ (TdDat name params _)) -> do
        tc      <- getType (J [] name)
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
        let tc' = abstractTyCon tc
        withoutConstructors tc' .
          withReplacedTyCons tc' .
            withTypes (name =:= tc') $
              k tc'
      _ -> terr "(BUG) Can't abstract non-datatypes"

-- | Run a computation in the context of a declaration
withDecl :: (Id i, Monad m) =>
            Decl i -> (Decl i -> TC m a) -> TC m a
withDecl decl k =
  let ?loc = getLoc decl in
    case decl of
      [$dc| let $x : $opt:t = $e |]
        -> withLet x t e $ \x' t' e' ->
             k [$dc| let $x' : $opt:t' = $e' |] 
      [$dc| type $list:tds |]
        -> withTyDecs tds $ \tds' ->
             k [$dc| type $list:tds' |]
      [$dc| abstype $list:at with $list:ds end |]
        -> withAbsTy at ds $ \at' ds' ->
             k [$dc| abstype $list:at' with $list:ds' end |]
      [$dc| module $uid:x = $b |]
        -> withMod x b $ \b' ->
             k [$dc| module $uid:x = $b' |]
      [$dc| open $b |]
        -> withOpen b $ \b' ->
             k [$dc| open $b' |]
      [$dc| local $list:ds0 with $list:ds1 end |]
        -> withLocal ds0 ds1 $ \ds0' ds1' ->
             k [$dc| local $list:ds0' with $list:ds1' end |]
      [$dc| exception $uid:n of $opt:mt |]
        -> withExn n mt $ \mt' ->
             k [$dc| exception $uid:n of $opt:mt' |]
      [$dc| $anti:a |] -> $antifail

-- | Run a computation in the context of a declaration sequence
withDecls :: (Id i, Monad m) =>
             [Decl i] -> ([Decl i] -> TC m a) -> TC m a
withDecls []     k = k []
withDecls (d:ds) k = withDecl d $ \d' ->
                       withDecls ds $ \ds' ->
                         k (d':ds')

-- | Type check a sequence of declarations
--
-- Returns information for printing new declarations in the REPL
tcDecls :: (Monad m, Id i) =>
           Bool -> S -> [Decl i] -> m (S, NewDefs, [Decl i])
tcDecls interactive gg ds =
  runTC gg $
    pushScope $
      withDecls ds $ \ds' -> do
        new <- askNewDefs
        squishScope $ do
          gg' <- saveTC interactive
          return (gg', new, ds')

-- Info about new defs for printing in the repl:
data NewDefs
  = NewDefs {
    -- | New declared tycons
    newTypes   :: T,
    -- | New declared values
    newValues  :: V,
    -- | New declared module names
    newModules :: [Uid]
  }

-- | No new definitions
emptyNewDefs :: NewDefs
emptyNewDefs  = (NewDefs empty empty [])

-- | Find out the new definitions (which live in the newest scope,
--   until we squish them down)
askNewDefs :: Monad m => TC m NewDefs
askNewDefs  = do
  scope <- askScope
  PEnv modenv level <- hideInvisible scope
  return NewDefs {
           newTypes   = tlevel level,
           newValues  = vlevel level,
           newModules = domain modenv
         }

-- | Add the type of a value binding
addVal :: (Ident :>: k, Monad m) =>
          S -> k -> Syntax.Type i -> m S
addVal gg x t = runTC gg $ do
  let ?loc = mkBogus "<addVal>"
  t' <- tcType t
  withAny (x' =:= t') $ saveTC False
    where x' :: Ident = liftKey x

-- | Add a type constructor binding
addType :: S -> Lid -> TyCon -> S
addType gg n td =
  gg { cEnv = cEnv gg =+= Level empty (n =:= td) }

-- | Add a new exception variant
addExn :: Monad m =>
          S -> Uid -> Maybe (Syntax.Type i) -> m S
addExn gg n mt =
  runTC gg $ do
    withExn n mt $ \_ ->
      saveTC False
  where ?loc = mkBogus "<addExn>"

-- | Add a nested submodule
addMod :: (Monad m) => S -> Uid -> (S -> m S) -> m S
addMod gg0 x k = do
  let env = cEnv gg0
      gg1 = gg0 { cEnv = genEmpty : env }
  gg2 <- k gg1
  let scope:_ = cEnv gg2
      gg3    = S { currIx = currIx gg2,
                   cEnv   = env =+= x =:= scope }
  return gg3

-- | Type check a program
tcProg :: (Monad m, Id i) => S -> Prog i -> m (Type, Prog i)
tcProg gg [$prQ| $list:ds in $opt:e0 |] =
  runTC gg $
    withDecls ds $ \ds' -> do
      (t, e') <- case e0 of
                   Just e  -> do
                     (t, e') <- tcExpr e
                     return (t, Just e')
                   Nothing -> do
                     return (tyUnit, Nothing)
      return (t, prog ds' e')

-- | The initial type-checking state
--
-- Binds the unit type and value, and the exception type @exn@
-- (both of which would be tricky to add using the 'BasisUtils'
-- facilities).
env0 :: S
env0  = S e0 0 where
  e0 :: E
  e0  = genEmpty =+= level0 where
    level0  = Level venv0 tenv0
    venv0   = Con (Uid "()") -:- tyUnit
    tenv0   = Lid "unit"     -:- tcUnit
          -+- Lid "exn"      -:- tcExn

-- | Reconstruct the declaration from a tycon binding, for printing
tyConToDec :: Id i => TyCon -> TyDec i
tyConToDec tc = case tc of
  _ | tc == tcExn
    -> tdAbs (Lid "exn") [] [] maxBound
  TyCon { tcName = n, tcNext = Just [(tp, rhs)] }
    -> tdSyn (jname n) [ tv | TpVar tv <- tp ] (typeToStx rhs)
  TyCon { tcName = n, tcCons = (ps, alts) }
    | not (isEmpty alts)
    -> tdDat (jname n) ps [ (uid, fmap typeToStx mt)
                          | (uid, mt) <- toList alts ]
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


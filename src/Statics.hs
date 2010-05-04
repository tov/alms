-- | The type checker
{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleContexts,
      FlexibleInstances,
      ImplicitParams,
      MultiParamTypeClasses,
      QuasiQuotes,
      ScopedTypeVariables,
      TemplateHaskell,
      TypeSynonymInstances #-}
module Statics (
  -- * Static environments
  S, env0,
  -- ** Environment construction
  addVal, addType, addExn, addMod,
  -- * Type checking
  tcProg, tcDecls,
  -- ** Type checking results for the REPL
  NewDefs(..), V, T, emptyNewDefs, TyInfo, tyInfoToDec
) where

import Quasi
import Util
import Syntax
import Loc
import Env as Env
import Ppr ()
import TypeRel
import Coercion (coerceExpression)

import Data.Data (Typeable, Data)
import Data.Generics (everywhere, mkT, everywhereM, mkM)
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Control.Monad.Reader as M.R
import qualified Control.Monad.State  as M.S
import qualified Control.Monad.RWS    as RWS

-- import System.IO.Unsafe (unsafePerformIO)
-- p :: (Show a) => a -> b -> b
-- p a b = unsafePerformIO (print a) `seq` b
-- p = const

-- Get the usage (sharing) of a variable in an expression:
usage :: QLid -> Expr i -> QLit
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- | The RHS of a tycon binding (abstract)
data TyInfo = TiAbs TyTag
            | TiSyn [TyVar] TypeT
            | TiDat TyTag [TyVar] (Env Uid (Maybe TypeT))
            | TiExn
  deriving (Data, Typeable)

-- Type environments
type D = Env TyVar TyVar       -- tyvars in scope, with idempot. renaming

-- | Mapping from identifiers to value types (includes datacons)
type V       = Env BIdent TypeT
-- | Mapping from type constructor names to tycon info
type T       = Env Lid TyInfo
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
instance GenLookup Level BIdent TypeT where
  level =..= k = vlevel level =..= k
instance GenLookup Level Lid TyInfo where
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
instance GenLookup TCEnv QLid TyInfo where
  TCEnv env _ =..= k = env =..= k
instance GenLookup TCEnv Ident TypeT where
  TCEnv env _ =..= k = env =..= k
instance GenLookup TCEnv TyVar TyVar where
  TCEnv _ d =..= k = d =..= k

instance GenExtend TCEnv Scope where
  TCEnv env dd =+= scope = TCEnv (env =+= scope) dd
instance GenExtend TCEnv Level where
  TCEnv env dd =+= level = TCEnv (env =+= level) dd
instance GenExtend TCEnv (Env Ident TypeT) where
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

-- | Abstract the given type by removing its datacon info
withoutConstructors :: Monad m =>
                       TyTag -> TC m a -> TC m a
withoutConstructors tag = TC . M.R.local clean . unTC where
  -- Note: only filters immediate scope -- should be right.
  clean (TCEnv env dd) = TCEnv (map eachScope env) dd
  eachScope      :: Scope -> Scope 
  eachScope scope = genModify scope emptyPath flevel
  flevel         :: Level -> Level
  flevel level    = level { vlevel = eachVe (vlevel level) }
  eachVe         :: V -> V
  eachVe          = fromList . filter keep . toList
  keep           :: (BIdent, TypeT) -> Bool
  keep (Con _, TyCon _ [_, TyCon _ _ tag'] _) = tag' /= tag
  keep (Con _, TyCon _ _ tag')                = tag' /= tag
  keep _                                      = True

-- | Repalce the type tag for the given type with the given
--   type tag while running a computation
withReplacedTyTags :: Monad m =>
                      TyTag -> TC m a -> TC m a
withReplacedTyTags tag = TC . M.R.local reptc . unTC
  where
    reptc (TCEnv env dd) = TCEnv (map (fmap replevel) env) dd
    replevel a = replaceTyTags tag a

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
          Ident -> TC m TypeT
getVar x = do
  t <- tryGetVar x
  t |! "Unbound variable: " ++ show x

-- | Try getting the type of a variable
tryGetVar :: Monad m =>
             Ident -> TC m (Maybe TypeT)
tryGetVar x = TC $ asksM (return . (=..= x))

-- | Get the info associated with a tycon, or fail
getType :: (?loc :: Loc, Monad m) => QLid -> TC m TyInfo
getType  = getAny "Unbound type constructor"

-- | Get the tag associated with a tycon, or fail (given a string to
--   identify the culprit
getTypeTag :: (?loc :: Loc, Monad m) => String -> QLid -> TC m TyTag
getTypeTag who n = do
  ti <- getType n
  case ti of
    TiAbs td     -> return td
    TiSyn _ _    -> terr $
      who ++ " expects an abstract or data type, but " ++
      "got type synonym: " ++ show n
    TiDat td _ _ -> return td
    TiExn        -> return tdExn

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
        String -> Type i -> String -> m a
tgot who got expected = terr $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- | Combination of 'tassert' and 'tgot'
tassgot :: (?loc :: Loc, Monad m) =>
           Bool -> String -> Type i -> String -> m ()
tassgot False = tgot
tassgot True  = \_ _ _ -> return ()

-- | Run a partial computation, and if it fails, substitute
--   the given failure message for the one generated
(|!) :: (?loc :: Loc, Monad m) => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> terr s
infix 1 |!

-- | Check type for closed-ness and and defined-ness, and add info
tcType :: (?loc :: Loc, Monad m) =>
          Type i -> TC m TypeT
tcType = tc where
  tc :: Monad m => Type i -> TC m TypeT
  tc [$ty| '$tv |] = do
    tv' <- getTV tv
    return (TyVar tv')
  tc [$ty| $t1 -[$q]> $t2 |] = do
    t1' <- tcType t1
    t2' <- tcType t2
    q'  <- qRepresent `liftM` qInterpretM q
    return [$ty|+ $t1' -[$q']> $t2' |]
  tc [$ty| ($list:ts) $qlid:n |] = do
    ts'  <- mapM tc ts
    tcon <- getType n
    case tcon of
      TiAbs td -> do
        checkLength (length (ttArity td))
        checkBound (ttBound td) ts'
        return (TyCon n ts' td)
      TiSyn ps t -> return (tysubsts ps ts' t)
      TiDat td _ _ -> do
        checkLength (length (ttArity td))
        checkBound (ttBound td) ts'
        return (TyCon n ts' td)
      TiExn      -> do
        checkLength 0
        return (TyCon n ts' tdExn)
    where
      checkLength len =
        tassert (length ts == len) $
          "Type constructor " ++ show n ++ " applied to " ++
          show (length ts) ++ " arguments where " ++
          show len ++ " expected"
      checkBound quals ts' =
        tassert (all2 (\qa t -> qualConst t <: qa) quals ts') $
          "Type constructor " ++ show n ++
          " used at " ++ show (map (qRepresent . qualifier) ts') ++
          " where at most " ++ show quals ++ " is permitted"
  tc [$ty| $quant:u '$tv . $t |] =
    withTVs [tv] $ \[tv'] -> TyQu u tv' `liftM` tc t
  tc [$ty| mu '$tv . $t |] = withTVs [tv] $ \[tv'] -> do
    t' <- tc t
    tassert (qualConst t' == tvqual tv) $
      "Recursive type " ++ show (TyMu tv t) ++ " qualifier " ++
      "does not match its own type variable."
    return (TyMu tv' t')
  tc [$ty| $anti:a |] = $antifail

-- | Remove all instances of t2 from t1, replacing with
--   a new type variable 
makeExType :: TypeT -> TypeT -> TypeT
makeExType t1 t2 = TyQu Exists tv $ everywhere (mkT erase) t1 where
  tv       = freshTyVar (TV (Lid "a") (qualConst t2)) (ftv [t1, t2])
  erase t' = if t' == t2 then TyVar tv else t'

-- | Type check an A expression
tcExpr :: Monad m => Expr i -> TC m (TypeT, ExprT)
tcExpr = tc where
  tc :: Monad m => Expr i -> TC m (TypeT, ExprT)
  tc e0 = let ?loc = getLoc e0 in case e0 of
    [$ex| $id:x |] -> do
      tx    <- getVar x
      let e' = [$ex|+ $id:x |] `setExn` findIsExn tx
      return (tx, e')
    [$ex| $str:s |] -> return ([$ty|+ string $td:string |], [$ex|+ $str:s |])
    [$ex| $int:z |] -> return ([$ty|+ int $td:int |],       [$ex|+ $int:z |])
    [$ex| $flo:f |] -> return ([$ty|+ float $td:float |],   [$ex|+ $flo:f |])
    [$ex| $antiL:a |] -> $antifail
    [$ex| match $e with $list:clauses |] -> do
      (t0, e') <- tc e
      (t1:ts, clauses') <- liftM unzip . forM clauses $ \ca -> do
        (gi, xi', ti, ei') <- withPatt t0 (capatt ca) $ tc (caexpr ca)
        checkSharing "match" gi (caexpr ca)
        return (ti, CaseAlt xi' ei')
      tr <- foldM (\ti' ti -> ti' \/? ti
                      |! "Mismatch in match/let: " ++ show ti ++
                          " and " ++ show ti')
            t1 ts
      return (tr, [$ex|+ match $e' with $list:clauses' |])
    [$ex| let rec $list:bs in $e2 |] -> do
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
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, [$ex|+ let rec $list:b's in $e2' |])
    [$ex| let $decl:d in $e2 |] ->
      withDecl d $ \d' -> do
        (t2, e2') <- tc e2
        return (t2, [$ex|+ let $decl:d' in $e2' |])
    [$ex| ($e1, $e2) |] -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return ([$ty|+ $t1 * $td:tuple $t2 |],
              [$ex|+ ($e1', $e2') |])
    [$ex| fun ($x : $t) -> $e |] -> do
      t' <- tcType t
      (gx, x', te, e') <- withPatt t' x $ tc e
      checkSharing "lambda" gx e
      q <- qRepresent `liftM` getWorthiness e0
      return ([$ty|+ $t' -[$q]> $te |],
              [$ex|+ fun ($x' : $t') -> $e' |])
    [$ex| $_ $_ |] -> do
      tcExApp tc e0
    [$ex| fun '$tv -> $e |] ->
      withTVs [tv] $ \[tv'] -> do
        tassert (syntacticValue e) $
          "Not a syntactic value under type abstraction: " ++ show e0
        (t, e') <- tc e
        return ([$ty|+ all '$tv'. $t |], [$ex|+ fun '$tv' -> $e' |])
    [$ex| $e1 [$t2] |] -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      t1'       <- tapply t1 t2'
      return (t1', [$ex|+ $e1' [$t2'] |])
    [$ex| Pack[$opt:mt1]($t2, $e) |] -> do
      t2'      <- tcType t2
      (te, e') <- tc e
      t1'      <- case mt1 of
        Just t1 -> tcType t1
        Nothing -> return (makeExType te t2')
      case t1' of
        [$ty| ex '$tv. $t11' |] -> do
          te' <- tapply [$ty|+ all '$tv. $t11' |] t2'
          tassert (te <: te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1'
          return (t1', [$ex| Pack[$t1']($t2', $e') |])
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
      tcExpr e1'' -- re-type check the coerced expression
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
           (Expr i -> TC m (TypeT, ExprT)) ->
           Expr i -> TC m (TypeT, ExprT)
tcExApp tc e0 = do
  let foralls t1 ts = do
        let (tvs, t1f) = unfoldTyQu Forall t1 -- peel off quantification
            (tas, _)   = unfoldTyFun t1f      -- peel off arg types
            nargs      = min (length tas) (length ts)
            tup ps     = TyCon (qlid "") (take nargs ps) tdTuple
        -- try to find types to unify formals and actuals, and apply
        t1' <- tryUnify tvs (tup tas) (tup ts) >>= foldM tapply t1
        arrows t1' ts
      arrows tr                   [] = return tr
      arrows t'@(TyQu Forall _ _) ts = foralls t' ts
      arrows [$ty| $ta -[$_]> $tr |] (t:ts) = do
        b <- unifies [] t ta
        tassgot b "Application (operand)" t (show ta)
        arrows tr ts
      arrows (TyMu tv t') ts = arrows (tysubst tv (TyMu tv t') t') ts
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
          TypeT -> TypeT -> m TypeT
tapply [$ty| all '$tv . $t1' |] t2 = do
  tassert (qualConst t2 <: tvqual tv) $
    "Type application cannot instantiate type variable " ++
    show tv ++ " with type " ++ show t2
  return (tysubst tv t2 t1')
tapply t1 _ = tgot "type application" t1 "(for)all type"

-- Given the type of thing to match and a pattern, return
-- the type environment bound by that pattern.
tcPatt :: (?loc :: Loc, Monad m) =>
          TypeT -> Patt -> TC m (D, V, Patt)
tcPatt t x0 = case x0 of
  [$pa| _ |]      -> return (empty, empty, x0)
  [$pa| $lid:x |] -> return (empty, Var x =:= t, x0)
  PaCon u mx _ -> case t of
    TyCon _ ts _ -> do
      tu <- getVar (fmap Con u)
      (params, mt, res) <- case unfoldTyQu Forall tu of
        (params, [$ty|+ $arg -> $res |])
          -> return (params, Just arg, res)
        (params, res)
          -> return (params, Nothing, res)
      tassgot (t <: tysubsts params ts res)
        "Pattern" t ("constructor " ++ show u)
      let isexn = findIsExn t
      case (mt, mx) of
        (Nothing, Nothing) ->
          return (empty, empty, PaCon u Nothing isexn)
        (Just t1, Just x1) -> do
          let t1' = tysubsts params ts t1
          (dx1, gx1, x1') <- tcPatt t1' x1
          return (dx1, gx1, PaCon u (Just x1') isexn)
        _ -> tgot "Pattern" t "wrong arity"
    _ -> tgot "Pattern" t ("constructor " ++ show u)
  [$pa| ($x, $y) |] -> do
    case t of
      [$ty|+ $xt * $td:tuple $yt |] -> do
          (dx, gx, x') <- tcPatt xt x
          (dy, gy, y') <- tcPatt yt y
          tassert (isEmpty (gx -|- gy)) $
            "Pattern " ++ show x0 ++ " binds variable twice"
          tassert (isEmpty (dx -|- dy)) $
            "Pattern " ++ show x0 ++ " binds type variable twice"
          return (dx =+= dy, gx =+= gy, [$pa| ($x', $y') |])
      _ -> tgot "Pattern " t "pair type"
  [$pa| $str:s |] -> do
      tassgot (tyinfo t == tdString)
        "Pattern" t "string"
      return (empty, empty, PaLit (LtStr s))
  [$pa| $int:z |] -> do
      tassgot (tyinfo t == tdInt)
        "Pattern" t "int"
      return (empty, empty, PaLit (LtInt z))
  [$pa| $flo:f |] -> do
      tassgot (tyinfo t == tdFloat)
        "Pattern" t "float"
      return (empty, empty, PaLit (LtFloat f))
  [$pa| $antiL:a |] -> $antifail
  [$pa| $x as $lid:y |] -> do
    (dx, gx, x') <- tcPatt t x
    let gy        = y =:= t
    tassert (isEmpty (gx -|- gy)) $
      "Pattern " ++ show x0 ++ " binds " ++ show y ++ " twice"
    return (dx, gx =+= gy, [$pa| $x' as $lid:y |])
  [$pa| Pack('$tv, $x) |] -> do
    case t of
      [$ty|+ ex '$tve. $te |] -> do
        tassert (tvqual tve <: tvqual tv) $
          "Cannot bind existential tyvar " ++ show tv ++
          " to " ++ show tve
        withTVs [tv] $ \[tv'] -> do
          let te' = tysubst tve (TyVar tv') te
          (dx, gx, x') <- tcPatt te' x
          tassert (dx =..= tv == Nothing) $
            "Pattern " ++ show x0 ++ " binds " ++ show tv ++ " twice"
          return (dx =+= tv =:+= tv', gx, [$pa| Pack('$tv', $x') |])
      _ -> tgot "Pattern" t "existential type"
  [$pa| $anti:a |] -> $antifail

-- | Run a computation in the context of the bindings from
--   a pattern.
withPatt :: (?loc :: Loc, Monad m) =>
            TypeT -> Patt -> TC m (TypeT, e) ->
            TC m (V, Patt, TypeT, e)
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
            [TyVar] -> TypeT -> TypeT -> m [TypeT]
tryUnify [] _ _        = return []
tryUnify (tv:tvs) t t' =
  case findSubst tv t t' of
    tguess:_ -> do
                  let subst' = tysubst tv tguess
                  tguesses <- tryUnify tvs (subst' t) t'
                  return (tguess : tguesses)
    _        -> terr $
                  "Cannot guess type t such that (" ++ show t ++
                  ")[t/" ++ show tv ++ "] ~ " ++ show t'

-- Given a type variable tv, type t in which tv may be free,
-- and a second type t', finds a plausible candidate to substitute
-- for tv to make t and t' unify.  (The answer it finds doesn't
-- have to be correct.
findSubst :: TyVar -> TypeT -> TypeT -> [TypeT]
findSubst tv = chk [] where
  chk, cmp :: [(TypeTEq, TypeTEq)] -> TypeT -> TypeT -> [TypeT]
  chk seen t1 t2 =
    let tw1 = TypeTEq t1; tw2 = TypeTEq t2
     in if (tw1, tw2) `elem` seen
          then []
          else cmp ((tw1, tw2) : seen) t1 t2

  cmp _    [$ty|+ '$tv' |] t'
    | tv == tv'    = [t']
  cmp seen [$ty|+ $t $qlid:_ $td:dual |] t'
                   = chk seen (dualSessionType t) t'
  cmp seen t' [$ty|+ $t $qlid:_ $td:dual |]
                   = chk seen t' (dualSessionType t)
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

  chkQe :: QExp TyVar -> QExp TyVar -> [TypeT]
  chkQe (QeVar tv1) (QeVar tv2) | tv1 == tv = [TyVar tv2]
                                | tv2 == tv = [TyVar tv1]
  chkQe (QeVar tv1) (QeLit Qu)  | tv1 == tv = [tyUnT]
  chkQe (QeLit Qu)  (QeVar tv2) | tv2 == tv = [tyUnT]
  chkQe (QeVar tv1) (QeLit Qa)  | tv1 == tv = [tyAfT]
  chkQe (QeLit Qa)  (QeVar tv2) | tv2 == tv = [tyAfT]
  chkQe _           _                       = []

-- | Convert qualset representations from a list of all tyvars and
--   list of qualifier-significant tyvars to a set of type parameter
--   indices
indexQuals :: (?loc :: Loc, Monad m) =>
              Lid -> [TyVar] -> QExp TyVar -> TC m (QExp Int)
indexQuals name tvs qexp = do
  qden <- qInterpretM qexp
  qRepresent `liftM` numberQDenM unbound tvs qden where
  unbound tv = terr $ "unbound tyvar " ++ show tv ++
                      " in qualifier list for type " ++ show name

-- BEGIN type decl checking

-- | Run a computation in the context of type declarations
withTyDecs :: (?loc :: Loc, Monad m) =>
              [TyDec i] -> ([TyDecT] -> TC m a) -> TC m a
withTyDecs tds0 k0 = do
  tassert (unique (map tdaName tds0)) $
    "Duplicate type(s) in recursive type declaration"
  let (atds, stds0, dtds) = foldr partition ([], [], []) tds0
  stds <- topSort getEdge stds0
  mapCont_ withStub dtds $
    let loop =
          mapCont withTyDec (atds ++ stds ++ dtds) $
            \tds'changed ->
              if any snd tds'changed
                then loop
                else k0 (map fst tds'changed)
     in loop
  where
    withStub (TdDat name params _) k = do
      index <- newIndex
      let tag = TyTag {
                  ttId    = index,
                  ttArity = map (const Omnivariant) params,
                  ttQual  = minBound,
                  ttBound = map tvqual params
                }
      withTypes (name =:= TiDat tag params empty) k
    withStub _           k = k
    --
    getEdge (TdSyn name _ t)    = (name, tyConsOfType t)
    getEdge (TdAbs name _ _ _)  = (name, S.empty)
    getEdge (TdDat name _ alts) = (name, names) where
       names = S.unions [ tyConsOfType t | (_, Just t) <- alts ]
    getEdge (TdAnti a)          = $antierror
    --
    partition td (atds, stds, dtds) =
      case td of
        TdAbs _ _ _ _ -> (td : atds, stds, dtds)
        TdSyn _ _ _   -> (atds, td : stds, dtds)
        TdDat _ _ _   -> (atds, stds, td : dtds)
        TdAnti a      -> $antierror

-- withTyDec types a type declaration, but in addition to
-- return (in CPS) a declaration, it returns a boolean that indicates
-- whether the type metadata has changed, which allows for iterating
-- to a fixpoint.
withTyDec :: (?loc :: Loc, Monad m) =>
             TyDec i -> ((TyDecT, Bool) -> TC m a) -> TC m a
withTyDec (TdAbs name params variances quals) k = do
  index  <- newIndex
  quals' <- indexQuals name params quals
  withTypes
    (name =:= TiAbs TyTag {
       ttId    = index,
       ttArity = variances,
       ttQual  = quals',
       ttBound = map tvqual params
     })
    (k (TdAbs name params variances quals, False))
withTyDec (TdSyn name params rhs) k = do
  (params', rhs') <- withTVs params $ \params' -> do
    rhs' <- tcType rhs
    return (params', rhs')
  withTypes (name =:= TiSyn params' rhs')
    (k (TdSyn name params' rhs', False))
withTyDec (TdDat name params alts) k = do
  TiDat tag _ _ <- getType (J [] name)
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
  let t'      = foldl tyTupleT tyUnitT [ t | (_, Just t) <- alts' ]
      arity   = typeVariances params' t'
      qual    = typeQual params' t'
      changed = arity /= ttArity tag
             || qual /= qInterpretCanonical (ttQual tag)
      tag'    = tag { ttArity = arity, ttQual = qRepresent qual }
  withTypes (name =:= TiDat tag' params' (fromList alts')) $
    withVars (alts2env name params' tag' alts') $
      (k (TdDat name params alts', changed))
withTyDec (TdAnti a) _ = $antifail

-- | Are all elements of the list unique?
unique :: Ord a => [a] -> Bool
unique  = loop S.empty where
  loop _    []     = True
  loop seen (x:xs) = x `S.notMember` seen && loop (S.insert x seen) xs

-- | Build an environment of datacon types from a datatype's
--   alternatives
alts2env :: Lid -> [TyVar] -> TyTag -> [(Uid, Maybe TypeT)] -> V
alts2env name params tag = fromList . map each where
  each (uid, Nothing) = (Con uid, alls result)
  each (uid, Just t)  = (Con uid, alls (t `tyArrI` result))
  alls t              = foldr tyAll t params
  result              = TyCon (J [] name) (map TyVar params) tag

-- | Compute the variances at which some type variables occur
--   in an open type expression
typeVariances :: [TyVar] -> TypeT -> [Variance]
typeVariances d0 = finish . ftvVs where
  finish m = [ maybe 0 id (M.lookup tv m)
             | tv <- d0 ]

-- | Compute the qualifier-significance of tyvars in an
--   open type expression
typeQual :: [TyVar] -> TypeT -> QDen Int
typeQual d0 = numberQDen d0 . loop where
  loop :: TypeT -> QDen TyVar
  loop [$ty|+ ($list:ts) $qlid:_ $info |]
    = denumberQDen (map loop ts) (qInterpret (ttQual info))
  loop [$ty|+ $_ -[$q]> $_ |]      = qInterpret q
  loop [$ty|+ '$tv |]              = qInterpret (QeVar tv)
  loop [$ty|+ $quant:_ '$tv. $t |] = qSubst tv minBound (loop t)
  loop [$ty|+ mu '$tv. $t |]       = qSubst tv minBound (loop t)
  loop [$ty|+ $anti:a |]           = $antierror

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

-- | The tycons that appear in a type
tyConsOfType :: Type i -> S.Set Lid
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
withLet :: (?loc :: Loc, Monad m) =>
           Patt -> Maybe (Type i) -> Expr i ->
           (Patt -> Maybe TypeT -> ExprT -> TC m a) -> TC m a
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
        "Type of top-level binding " ++ show x ++ " is not unlimited"
      return te
  (d, g, x') <- tcPatt t' x
  tassert (isEmpty d) $
    "Cannot unpack existential in top-level binding"
  withVars g $
    k x' (Just t') e'

-- | Run a computation in the context of a module open declaration
withOpen :: (?loc :: Loc, Monad m) =>
            ModExp i -> (ModExpT -> TC m a) -> TC m a
withOpen b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [] [scope]
  withAny scope' $ k b'

-- | Run a computation in the context of a local block (that is, after
--   the block)
withLocal :: (?loc :: Loc, Monad m) =>
             [Decl i] -> [Decl i] ->
             ([DeclT] -> [DeclT] -> TC m a) -> TC m a
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
           Uid -> Maybe (Type i) ->
           (Maybe TypeT -> TC m a) -> TC m a
withExn n mt k = do
  mt'   <- gmapM tcType mt
  withVars (Con n =:= maybe tyExnT (`tyArrI` tyExnT) mt') $
    k mt'

-- Is the given type the type of an exception constructor?
findIsExn :: TypeT -> Bool
findIsExn [$ty|+ $_ -> $qlid:_ $td:exn |] = True
findIsExn [$ty|+ $qlid:_ $td:exn |] = True
findIsExn _ = False

-- | Run a computation in the context of a module
withMod :: (?loc :: Loc, Monad m) =>
           Uid -> ModExp i -> (ModExpT -> TC m a) -> TC m a
withMod x b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [x] [scope]
  withAny (x =:= scope') $ k b'

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
    repair :: Monad m => TypeT -> TC m TypeT
    repair t@(TyCon name _ tag) = do
      mtd <- tryGetAny name
      return $ case mtd of
        Just (TiAbs tag')
          | tag' == tag  -> t
        Just (TiDat tag' _ _)
          | tag' == tag  -> t
        Just (TiSyn _ _) -> t
        Just TiExn
          | tdExn == tag -> t
        _                -> t `setTycon` hide (tyinfo t) name
    repair t = return t

    hide :: TyTag -> QLid -> QLid
    hide _   name@(J (Uid "?" : _) _) = name
    hide tag (J qs (Lid k)) =
      J (Uid "?":qs) (Lid (k ++ ':' : show (ttId tag)))

-- | Replace the printing name of each type with the shortest
--   path to access that type.  (So unnecessary!)
requalifyTypes :: [Uid] -> E -> E
requalifyTypes uids env = map (fmap repairLevel) env where
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

-- | Type check a module body
tcModExp :: (?loc :: Loc, Monad m) =>
             ModExp i -> TC m (ModExpT, Scope)
tcModExp (MeStr ds) =
  pushScope $
    withDecls ds $ \ds' -> do
      scope <- askScope
      return (MeStr ds', scope)
tcModExp (MeName n)   = do
  scope <- getModule n
  return (MeName n, scope)
tcModExp (MeAnti a)   = $antifail

-- | Run a computation in the context of an abstype block
withAbsTy :: (?loc :: Loc, Monad m) =>
             [AbsTy i] -> [Decl i] ->
             ([AbsTyT] -> [DeclT] -> TC m a) ->
             TC m a
withAbsTy atds ds k0 =
  let vars  = map atvariance atds
      quals = map atquals atds
      tds   = map atdecl atds in
  withTyDecs tds $ \tds' ->
    withDecls ds $ \ds' ->
      mapCont absDecl atds $ \tags' ->
        k0 (zipWith3 AbsTy vars quals tds')
           (foldr replaceTyTags ds' tags')
  where
    absDecl (AbsTy arity quals (TdDat name params _)) k = do
      tag     <- getTypeTag "abstract-with-end" (J [] name)
      qualSet <- indexQuals name params quals
      tassert (length params == length (ttArity tag)) $
        "abstract-with-end: " ++ show (length params) ++
        " given for type " ++ show name ++
        " which has " ++ show (length (ttArity tag))
      tassert (all2 (<:) (ttArity tag) arity) $
        "abstract-with-end: declared arity for type " ++ show name ++
        ", " ++ show arity ++
        ", is more general than actual arity " ++ show (ttArity tag)
      tassert (qInterpretCanonical (ttQual tag) <:
               qInterpretCanonical qualSet) $ 
        "abstract-with-end: declared qualifier for type " ++ show name ++
        ", " ++ show qualSet ++
        ", is more general than actual qualifier " ++ show (ttQual tag)
      let tag' = TyTag (ttId tag) arity qualSet (map tvqual params)
      withoutConstructors tag' .
        withReplacedTyTags tag' .
          withTypes (name =:= TiAbs tag') $
            k tag'
    absDecl _ _ = terr "(BUG) Can't abstract non-datatypes"

-- | Run a computation in the context of a declaration
withDecl :: Monad m =>
            Decl i -> (DeclT -> TC m a) -> TC m a
withDecl decl k =
  let ?loc = getLoc decl in
    case decl of
      DcLet loc x t e ->  withLet x t e (\x' t' -> k . DcLet loc x' t')
      DcTyp loc tds   ->  withTyDecs tds (k . DcTyp loc)
      DcAbs loc at ds ->  withAbsTy at ds ((.) k . DcAbs loc)
      DcMod loc x b   ->  withMod x b (k . DcMod loc x)
      DcOpn loc b     ->  withOpen b (k . DcOpn loc)
      DcLoc loc d0 d1 ->  withLocal d0 d1 ((.) k . DcLoc loc)
      DcExn loc n mt  ->  withExn n mt (k . DcExn loc n)
      DcAnti a        ->  $antifail

-- | Run a computation in the context of a declaration sequence
withDecls :: Monad m =>
             [Decl i] -> ([DeclT] -> TC m a) -> TC m a
withDecls []     k = k []
withDecls (d:ds) k = withDecl d $ \d' ->
                       withDecls ds $ \ds' ->
                         k (d':ds')

-- | Type check a sequence of declarations
--
-- Returns information for printing new declarations in the REPL
tcDecls :: Monad m => Bool -> S -> [Decl i] -> m (S, NewDefs, [DeclT])
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
          S -> k -> Type i -> m S
addVal gg x t = runTC gg $ do
  let ?loc = mkBogus "<addVal>"
  t' <- tcType t
  withAny (x' =:= t') $ saveTC False
    where x' :: Ident = liftKey x

-- | Add a type constructor binding
addType :: S -> Lid -> TyTag -> S
addType gg n td =
  gg { cEnv = cEnv gg =+= Level empty (n =:= TiAbs td) }

-- | Add a new exception variant
addExn :: Monad m =>
          S -> Uid -> Maybe (Type i) -> m S
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
tcProg :: Monad m => S -> Prog i -> m (TypeT, ProgT)
tcProg gg (Prog ds e0) =
  runTC gg $
    withDecls ds $ \ds' -> do
      (t, e') <- case e0 of
                   Just e  -> do
                     (t, e') <- tcExpr e
                     return (t, Just e')
                   Nothing -> do
                     return (tyUnitT, Nothing)
      return (t, Prog ds' e')

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
    venv0   = Con (Uid "()")    -:- tyUnitT
    tenv0   = Lid "unit" -:- TiDat tdUnit [] (
                Uid "()"    -:- Nothing
              ) -+-
              Lid "exn"  -:- TiExn

-- | Reconstruct the declaration from a tycon binding, for printing
tyInfoToDec :: Lid -> TyInfo -> TyDec ()
tyInfoToDec n ti = case ti of
  TiSyn ps rhs    -> TdSyn n ps (removeTyTags rhs)
  TiDat _ ps alts -> TdDat n ps [ (uid, fmap removeTyTags mt)
                                      | (uid, mt) <- toList alts ]
  TiAbs tag       ->
    let tyvars   = zipWith (TV . Lid) alphabet (ttBound tag)
        alphabet = map return ['a' .. 'z'] ++
                   [ x ++ [y] | x <- alphabet, y <- ['a' .. 'z'] ]
     in TdAbs n (zipWith const tyvars (ttArity tag))
              (ttArity tag)
              (qRepresent
                (denumberQDen
                  (map (qInterpret . QeVar) tyvars)
                  (qInterpretCanonical (ttQual tag))))
  TiExn           -> TdAbs (Lid "exn") [] [] maxBound


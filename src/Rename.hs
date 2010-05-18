{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      QuasiQuotes,
      RankNTypes,
      RelaxedPolyRec,
      TemplateHaskell #-}
module Rename (
  -- * The renaming monad and runners
  Renaming, runRenaming, runRenamingM,
  renameMapM,
  -- * State between renaming steps
  RenameState, renameState0,
  -- ** Adding the basis
  addVal, addType, addMod,
  -- * Renamers
  renameProg, renameDecls, renameDecl, renameType,
) where

import Meta.Quasi
import Syntax hiding ((&))
import qualified Loc
import qualified Syntax.Decl
import qualified Syntax.Expr
import qualified Syntax.Notable
import qualified Syntax.Patt
import Util

import Data.Monoid
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.RWS as RWST
import qualified Control.Monad.State  as M.S
import qualified Control.Monad.Error  ()

-- | The type to save the state of the renamer between calls
data RenameState = RenameState {
  savedEnv     :: Env,
  savedCounter :: Renamed
} deriving Show

-- | The initial state
renameState0 :: RenameState
renameState0  = RenameState {
  savedEnv      = mempty {
    datacons = M.singleton (uid "()") (uid "()")
  },
  savedCounter  = renamed0
}

-- | The renaming monad: Reads a context, writes a module, and
--   keeps track of a renaming counter state.
newtype Renaming a = R {
  unR :: RWST Context Module Renamed (Either String) a
} deriving Functor

instance Monad Renaming where
  return  = R . return
  m >>= k = R (unR m >>= unR . k)
  fail s  = R $ do
    loc <- asks location
    fail $ if isBogus loc
      then s
      else show loc ++ ":\n" ++ s

instance MonadWriter Module Renaming where
  listen = R . listen . unR
  tell   = R . tell
  pass   = R . pass . unR

instance MonadReader Env Renaming where
  ask     = R (asks env)
  local f = R . local (\cxt -> cxt { env = f (env cxt) }) . unR

-- | The renaming environment
data Env = Env {
  tycons, vars    :: !(M.Map (Lid Raw) (Lid Renamed)),
  datacons        :: !(M.Map (Uid Raw) (Uid Renamed)),
  modules         :: !(M.Map (Uid Raw) (Uid Renamed, Module, Env)),
  tyvars          :: !(M.Map (TyVar Raw) (TyVar Renamed, Bool))
} deriving Show

-- | A module item is one of 5 renaming entries.  Note that while
--   type variables are not actual module items, they are exported from
--   patterns, so it's useful to have them here.
data Module
  = MdNil
  | MdApp     !Module      !Module
  | MdTycon   !(Lid Raw)   !(Lid Renamed)
  | MdVar     !(Lid Raw)   !(Lid Renamed)
  | MdDatacon !(Uid Raw)   !(Uid Renamed)
  | MdModule  !(Uid Raw)   !(Uid Renamed) !Module
  | MdTyvar   !(TyVar Raw) !(TyVar Renamed)
  deriving Show

-- | The renaming context, which includes the environment (which is
--   persistant), and other information with is not
data Context = Context {
  env      :: Env,
  allocate :: Bool,
  location :: Loc
}

-- | Run a renaming computation
runRenaming :: Bool -> RenameState -> Renaming a ->
               Either String (a, RenameState)
runRenaming nonTrivial saved action = do
  (result, counter, md) <-
    runRWST (unR action)
      Context {
        env      = savedEnv saved,
        allocate = nonTrivial,
        location = bogus
      }
      (savedCounter saved)
  let env' = savedEnv saved `mappend` envify md
  return (result, RenameState env' counter)

-- | Run a renaming computation
runRenamingM :: Monad m =>
                Bool -> RenameState -> Renaming a -> m (a, RenameState)
runRenamingM  = either fail return <$$$> runRenaming

-- | Alias
type R a  = Renaming a

instance Monoid Env where
  mempty = Env M.empty M.empty M.empty M.empty M.empty
  mappend (Env a1 a2 a3 a4 a5) (Env b1 b2 b3 b4 b5) =
    Env (a1 & b1) (a2 & b2) (a3 & b3) (a4 & b4) (a5 & b5)
      where a & b = M.union b a

instance Monoid Module where
  mempty  = MdNil
  mappend = MdApp

-- | Open a module into an environment
envify :: Module -> Env
envify MdNil            = mempty
envify (MdApp md1 md2)  = envify md1 `mappend` envify md2
envify (MdTycon l l')   = mempty { tycons = M.singleton l l' }
envify (MdVar l l')     = mempty { vars = M.singleton l l' }
envify (MdDatacon u u') = mempty { datacons = M.singleton u u' }
envify (MdModule u u' md)
                        = mempty { modules = M.singleton u (u',md,envify md) }
envify (MdTyvar tv tv') = mempty { tyvars = M.singleton tv (tv', True) }

-- | Like 'asks', but in the 'R' monad
withContext :: (Context -> R a) -> R a
withContext  = R . (ask >>=) . fmap unR

-- | Run in the context of a given source location
withLoc :: Locatable loc => loc -> R a -> R a
withLoc loc = R . local (\cxt -> cxt { location = getLoc loc }) .  unR

-- | Append a module to the current environment
inModule :: Module -> R a -> R a
inModule m = local (\e -> e `mappend` envify m)

-- | Generate an unbound name error
unbound :: Show a => String -> a -> R b
unbound ns a = fail $ ns ++ " not in scope: `" ++ show a ++ "'"

-- | Are all keys of the list unique?  If not, return a pair of
--   values
unique       :: Ord a => (b -> a) -> [b] -> Maybe (b, b)
unique getKey = loop M.empty where
  loop _    []     = Nothing
  loop seen (x:xs) =
    let k = getKey x
     in case M.lookup k seen of
          Nothing -> loop (M.insert k x seen) xs
          Just x' -> Just (x', x)

-- | Grab the module produced by a computation, and
--   produce no module
steal :: R a -> R (a, Module)
steal = R . censor (const mempty) . listen . unR

-- | Get all the names, included qualified, bound in a module
getAllVariables :: Module -> [QLid Renamed]
getAllVariables = S.toList . loop where
  loop (MdApp md1 md2)    = loop md1 `S.union` loop md2
  loop (MdVar _ l')       = S.singleton (J [] l')
  loop (MdModule _ u' md) = S.mapMonotonic (\(J us l) -> J (u':us) l)
                                           (loop md)
  loop _                  = S.empty

-- | Temporarily hide the type variables in scope, and pass the
--   continuation a function to bring them back
hideTyvars :: R a -> R a
hideTyvars  =
  local (\e -> e { tyvars = M.map (second (const False)) (tyvars e) })

-- | Look up something in the environment
getGeneric :: (Ord k, Show k) =>
              String -> (Env -> M.Map k k') ->
              Path (Uid Raw) k -> R (Path (Uid Renamed) k')
getGeneric what prj qx0 = withContext (loop [] qx0 . env) where
  loop ms' (J []     x) e = case M.lookup x (prj e) of
    Just x' -> return (J (reverse ms') x')
    Nothing -> unbound what qx0
  loop ms' (J (m:ms) x) e = case M.lookup m (modules e) of
    Just (m', _, e') -> loop (m':ms') (J ms x) e'
    Nothing          -> unbound "module" (J (reverse ms') m)

-- | Look up a variable in the environment
getVar :: QLid Raw -> R (QLid Renamed)
getVar  = getGeneric "variable" vars

-- | Look up a data constructor in the environment
getDatacon :: QUid Raw -> R (QUid Renamed)
getDatacon  = getGeneric "data constructor" datacons

-- | Look up a variable in the environment
getTycon :: QLid Raw -> R (QLid Renamed)
getTycon  = getGeneric "type constructor" tycons

-- | Look up a module in the environment
getModule :: QUid Raw -> R (QUid Renamed, Module, Env)
getModule  = liftM pull . getGeneric "module" modules
  where
    pull (J ps (qu, m, e)) = (J ps qu, m, e)

-- | Look up a variable in the environment
getTyvar :: TyVar Raw -> R (TyVar Renamed)
getTyvar tv = do
  e <- asks tyvars
  case M.lookup tv e of
    Nothing           -> fail $ "type variable not in scope: " ++ show tv
    Just (tv', True)  -> return tv'
    Just (_,   False) -> fail $
      "type variable not in scope: " ++ show tv ++ "\n" ++
      "NB: Nested declarations cannot see tyvars from their parent expression."

-- | Get a new name for a variable binding
bindGeneric :: (Ord ident, Show ident, Antible ident) =>
               (Renamed -> ident -> ident') ->
               (ident -> ident' -> Module) ->
               ident -> R ident'
bindGeneric ren build x = R $ do
  case prjAnti x of
    Just a  -> $antifail
    Nothing -> return ()
  doAlloc <- asks allocate
  x' <- if doAlloc
    then do
      counter <- M.S.get
      M.S.put (succ counter)
      return (ren counter x)
    else do
      return (ren trivialId x)
  tell (build x x')
  return x'

-- | Get a new name for a variable binding
bindVar :: Lid Raw -> R (Lid Renamed)
bindVar  = bindGeneric (\r -> Lid r . unLid) MdVar

-- | Get a new name for a variable binding
bindTycon :: Lid Raw -> R (Lid Renamed)
bindTycon  = bindGeneric (\r -> Lid r . unLid) MdTycon

-- | Get a new name for a data constructor binding
bindDatacon :: Uid Raw -> R (Uid Renamed)
bindDatacon = bindGeneric (\r u -> (Uid r (unUid u))) MdDatacon

-- | Get a new name for a module, and bind it in the environment
bindModule :: Uid Raw -> Module -> R (Uid Renamed)
bindModule u0 md =
  bindGeneric (\r u -> Uid r (unUid u)) (\u u' -> MdModule u u' md) u0

-- | Add a type variable to the scope
bindTyvar :: TyVar Raw -> R (TyVar Renamed)
bindTyvar = bindGeneric (\r (TV l q) -> TV (Lid r (unLid l)) q) MdTyvar

-- | Map a function over a list, allowing the exports of each item
--   to be in scope for the rest
renameMapM :: (a -> R b) -> [a] -> R [b]
renameMapM _ []     = return []
renameMapM f (x:xs) = do
  (x', md) <- listen (f x)
  xs' <- inModule md $ renameMapM f xs
  return (x':xs')

-- | Rename a program
renameProg :: Prog Raw -> R (Prog Renamed)
renameProg [$prQ| $list:ds in $opt:me1 |] = do
  (ds', md) <- listen $ renameDecls ds
  me1' <- inModule md $ gmapM renameExpr me1
  return [$prQ|+ $list:ds' in $opt:me1' |]

-- | Rename a list of declarations and return the environment
--   that they bind
renameDecls :: [Decl Raw] -> R [Decl Renamed]
renameDecls  = renameMapM renameDecl

-- | Rename a declaration and return the environment that it binds
renameDecl :: Decl Raw -> R (Decl Renamed)
renameDecl d0 = case d0 of
  [$dc| let $x : $opt:mt = $e |] -> do
    x'  <- renamePatt x
    mt' <- gmapM renameType mt
    e'  <- renameExpr e
    return [$dc|+ let $x' : $opt:mt' = $e' |]
  [$dc| type $list:tds |] -> do
    let bindEach [$tdQ| $anti:a |] = $antifail
        bindEach (N note td)       = do
          bindTycon (tdName td)
          return (tdName td, getLoc note)
    (llocs, md) <- listen $ mapM bindEach tds
    case unique fst llocs of
      Nothing -> return ()
      Just ((l, loc1), (_, loc2)) -> fail $
        "type `" ++ show l ++ "' declared twice in type group at " ++
        show loc1 ++ " and " ++ show loc2
    tds' <- inModule md $ mapM (liftM snd . renameTyDec Nothing) tds
    return [$dc|+ type $list:tds' |]
  [$dc| abstype $list:ats with $list:ds end |] -> do
    let bindEach [$atQ| $anti:a |] = $antifail
        bindEach (N _ (AbsTy _ _ [$tdQ| $anti:a |])) = $antifail
        bindEach (N note at) = do
          let l = (tdName (dataOf (atdecl at)))
          bindTycon l
          return (l, getLoc note)
    (llocs, mdT) <- listen $ mapM bindEach ats
    case unique fst llocs of
      Nothing -> return ()
      Just ((l, loc1), (_, loc2)) -> fail $
        "type `" ++ show l ++ "' declared twice in abstype group at " ++
        show loc1 ++ " and " ++ show loc2
    (ats', mdD) <-
      steal $
        inModule mdT $
          forM ats $ \at -> withLoc at $ case dataOf at of
            AbsTy variances qe td -> do
              (Just qe', td') <- renameTyDec (Just qe) td
              return (absTy variances qe' td' <<@ at)
            AbsTyAnti a -> $antifail
    -- Don't tell mdD upward, since we're censoring the datacons
    ds' <- inModule (mdT `mappend` mdD) $ renameDecls ds
    return [$dc|+ abstype $list:ats' with $list:ds' end |]
  [$dc| module INTERNALS = $me1 |] ->
    R $ local (\context -> context { allocate = False }) $ unR $ do
      let u = uid "INTERNALS"
      (me1', md) <- steal $ renameModExp me1
      u' <- bindModule u md
      return [$dc|+ module $uid:u' = $me1' |]
  [$dc| module $uid:u = $me1 |] -> do
    (me1', md) <- steal $ renameModExp me1
    u' <- bindModule u md
    return [$dc|+ module $uid:u' = $me1' |]
  [$dc| open $me1 |] -> do
    me1' <- renameModExp me1
    return [$dc|+ open $me1' |]
  [$dc| local $list:ds1 with $list:ds2 end |] -> do
    (ds1', md) <- steal $ renameDecls ds1
    ds2' <- inModule md $ renameDecls ds2
    return [$dc| local $list:ds1' with $list:ds2' end |]
  [$dc| exception $uid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- gmapM renameType mt
    return [$dc|+ exception $uid:u' of $opt:mt' |]
  [$dc| $anti:a |] -> $antifail

renameTyDec :: Maybe (QExp Raw) -> TyDec Raw ->
               R (Maybe (QExp Renamed), TyDec Renamed)
renameTyDec _   (N _ (TdAnti a)) = $antierror
renameTyDec mqe (N note td)      = withLoc note $ do
  J [] l' <- getTycon (J [] (tdName td))
  let tvs = tdParams td
  case unique id tvs of
    Nothing      -> return ()
    Just (tv, _) -> fail $
      "type variable " ++ show tv ++ " repeated in type parameters"
  (tvs', mdTvs) <- steal $ mapM bindTyvar tvs
  inModule mdTvs $ do
    mqe' <- gmapM renameQExp mqe
    td'  <- case td of
      TdAbs _ _ variances qe -> do
        qe' <- renameQExp qe
        return (tdAbs l' tvs' variances qe')
      TdSyn _ _ t -> do
        t' <- renameType t
        return (tdSyn l' tvs' t')
      TdDat _ _ cons -> do
        cons' <- forM cons $ \(u, mt) -> do
          u'    <- bindDatacon u
          mt'   <- gmapM renameType mt
          return (u', mt')
        return (tdDat l' tvs' cons')
      TdAnti a -> $antifail
    return (mqe', td' <<@ note)

renameModExp :: ModExp Raw -> R (ModExp Renamed)
renameModExp me0 = case me0 of
  [$me| struct $list:ds end |] -> do
    ds' <- renameDecls ds
    return [$me|+ struct $list:ds' end |]
  [$me| $quid:qu $list:_ |] -> do
    (qu', md, _) <- getModule qu
    let qls = getAllVariables md
    tell md
    return [$me|+ $quid:qu' $list:qls |]
  [$me| $anti:a |] -> $antifail

-- | Rename an expression
renameExpr :: Expr Raw -> R (Expr Renamed)
renameExpr e0 = withLoc e0 $ case e0 of
  [$ex| $id:x |] -> case view x of
    Left ql -> do
      ql' <- getVar ql
      let x' = fmap Var ql'
      return [$ex|+ $id:x' |]
    Right qu -> do
      qu' <- getDatacon qu
      let x' = fmap Con qu'
      return [$ex|+ $id:x' |]
  [$ex| $lit:lit |] -> do
    lit' <- renameLit lit
    return [$ex|+ $lit:lit' |]
  [$ex| match $e1 with $list:cas |] -> do
    e1'  <- renameExpr e1
    cas' <- mapM renameCaseAlt cas
    return [$ex|+ match $e1' with $list:cas' |]
  [$ex| let rec $list:bns in $e |] -> do
    (bns', md) <- renameBindings bns
    e' <- inModule md $ renameExpr e
    return [$ex|+ let rec $list:bns' in $e' |]
  [$ex| let $decl:d in $e |] -> do
    (d', md) <- steal $ hideTyvars $ renameDecl d
    e' <- inModule md (renameExpr e)
    return [$ex|+ let $decl:d' in $e' |]
  [$ex| ($e1, $e2) |] -> do
    e1' <- renameExpr e1
    e2' <- renameExpr e2
    return [$ex|+ ($e1', $e2') |]
  [$ex| fun $x : $t -> $e |] -> do
    t' <- renameType t
    (x', md) <- steal $ renamePatt x
    e' <- inModule md $ renameExpr e
    return [$ex|+ fun $x' : $t' -> $e' |]
  [$ex| $e1 $e2 |] -> do
    e1' <- renameExpr e1
    e2' <- renameExpr e2
    return [$ex|+ $e1' $e2' |]
  [$ex| fun '$tv -> $e |] -> do
    (tv', md) <- steal $ bindTyvar tv
    e' <- inModule md $ renameExpr e
    return [$ex|+ fun '$tv' -> $e' |]
  [$ex| $e [$t] |] -> do
    e' <- renameExpr e
    t' <- renameType t
    return [$ex|+ $e' [$t'] |]
  [$ex| Pack[$opt:mt]($t, $e) |] -> do
    mt' <- gmapM renameType mt
    t'  <- renameType t
    e'  <- renameExpr e
    return [$ex|+ Pack[$opt:mt']($t', $e') |]
  [$ex| ( $e : $opt:mt :> $t) |] -> do
    e'  <- renameExpr e
    mt' <- gmapM renameType mt
    t'  <- renameType t
    return [$ex| ( $e' : $opt:mt' :> $t') |]
  [$ex| $anti:a |] -> $antifail

-- | Rename a literal (no-op, except fails on antiquotes)
renameLit :: Lit -> R Lit
renameLit lit0 = case lit0 of
  LtAnti a -> $antifail
  _        -> return lit0

-- | Rename a case alternative
renameCaseAlt :: CaseAlt Raw -> R (CaseAlt Renamed)
renameCaseAlt ca0 = withLoc ca0 $ case ca0 of
  [$caQ| $x -> $e |] -> do
    (x', md) <- steal $ renamePatt x
    e' <- inModule md $ renameExpr e
    return [$caQ|+ $x' -> $e' |]
  [$caQ| $antiC:a |] -> $antifail

-- | Rename a set of let rec bindings
renameBindings :: [Binding Raw] -> R ([Binding Renamed], Module)
renameBindings bns = do
  lxtes <- forM bns $ \bn ->
    case bn of
      [$bnQ| $lid:x : $t = $e |] -> return (_loc, x, t, e)
      [$bnQ| $antiB:a |] -> $antifail
  case unique (\(_,x,_,_) -> x) lxtes of
    Nothing          -> return ()
    Just ((l1,x,_,_),(l2,_,_,_)) -> fail $
      "variable `" ++ show x ++ "' bound twice in let rec at " ++
      show l1 ++ " and " ++ show l2
  let bindEach (rest, env') (l,x,t,e) = do
        (x', env'') <- steal $ bindVar x
        return ((l,x',t,e):rest, env' `mappend` env'')
  (lxtes', md) <- foldM bindEach ([], mempty) lxtes
  bns' <- inModule md $
            forM (reverse lxtes') $ \(l,x',t,e) -> withLoc l $ do
              let _loc = l
              t'  <- renameType t
              e'  <- renameExpr e
              return [$bnQ|+ $lid:x' : $t' = $e' |]
  return (bns', md)

-- | Rename a type
renameType :: Type Raw -> R (Type Renamed)
renameType t0 = case t0 of
  [$ty| ($list:ts) $qlid:ql |] -> do
    ql' <- getTycon ql
    ts' <- mapM renameType ts
    return [$ty|+ ($list:ts') $qlid:ql' |]
  [$ty| '$tv |] -> do
    tv' <- getTyvar tv
    return [$ty|+ '$tv' |]
  [$ty| $t1 -[$qe]> $t2 |] -> do
    t1' <- renameType t1
    qe' <- renameQExp qe
    t2' <- renameType t2
    return [$ty|+ $t1' -[$qe']> $t2' |]
  [$ty| $quant:u '$tv. $t |] -> do
    (tv', md) <- steal $ bindTyvar tv
    t' <- inModule md $ renameType t
    return [$ty|+ $quant:u '$tv'. $t' |]
  [$ty| mu '$tv. $t |] -> do
    (tv', md) <- steal $ bindTyvar tv
    t' <- inModule md $ renameType t
    return [$ty|+ mu '$tv'. $t' |]
  [$ty| $anti:a |] -> $antifail

-- | Rename a qualifier expression
renameQExp :: QExp Raw -> R (QExp Renamed)
renameQExp qe0 = case qe0 of
  [$qeQ| $qlit:qlit |] -> do
    return [$qeQ|+ $qlit:qlit |]
  [$qeQ| $qvar:tv |] -> do
    tv' <- getTyvar tv
    return [$qeQ| $qvar:tv' |]
  [$qeQ| $qdisj:qes |] -> do
    qes' <- mapM renameQExp qes
    return [$qeQ| $qdisj:qes' |]
  [$qeQ| $qconj:qes |] -> do
    qes' <- mapM renameQExp qes
    return [$qeQ| $qconj:qes' |]
  [$qeQ| $anti:a |] -> do
    $antifail

-- | Rename a pattern and run a continuation in its context
renamePatt :: Patt Raw -> R (Patt Renamed)
renamePatt x00 =
  withLoc x00 $
    M.S.evalStateT (loop x00) M.empty where
  loop :: Patt Raw ->
          M.S.StateT (M.Map (Either (Lid Raw) (TyVar Raw)) Loc)
            Renaming (Patt Renamed)
  loop x0 = case x0 of
    [$pa| _ |] ->
      return [$pa|+ _ |]
    [$pa| $lid:l |] -> do
      l' <- var _loc l
      return [$pa|+ $lid:l' |]
    [$pa| $quid:qu |] -> do
      qu' <- M.S.lift $ getDatacon qu
      return [$pa|+ $quid:qu' |]
    [$pa| $quid:qu $x |] -> do
      qu' <- M.S.lift $ getDatacon qu
      x' <- loop x
      return [$pa|+ $quid:qu' $x' |]
    [$pa| ($x1, $x2) |] -> do
      x1' <- loop x1
      x2' <- loop x2
      return [$pa|+ ($x1', $x2') |]
    [$pa| $lit:lit |] -> do
      lit' <- M.S.lift $ renameLit lit
      return [$pa|+ $lit:lit' |]
    [$pa| $x as $lid:l |] -> do
      x' <- loop x
      l' <- var _loc l
      return [$pa|+ $x' as $lid:l' |]
    [$pa| Pack('$tv, $x) |] -> do
      tv' <- tyvar _loc tv
      x'  <- loop x
      return [$pa|+ Pack('$tv', $x') |]
    [$pa| $anti:a |] -> do
      $antifail
  --
  var loc1 l = do
    seen <- M.S.get
    case M.lookup (Left l) seen of
      Just loc2 -> fail $
        "variable `" ++ show l ++ "' bound twice in pattern at " ++
        show loc1 ++ " and " ++ show loc2
      Nothing   -> do
        M.S.put (M.insert (Left l) loc1 seen)
        M.S.lift (bindVar l)
  --
  tyvar loc1 tv = do
    seen <- M.S.get
    case M.lookup (Right tv) seen of
      Just loc2 -> fail $
        "type variable " ++ show tv ++ " bound twice in pattern at " ++
        show loc1 ++ " and " ++ show loc2
      Nothing   -> do
        M.S.put (M.insert (Right tv) loc1 seen)
        M.S.lift (bindTyvar tv)

addVal     :: Lid Raw -> R (Lid Renamed)
addType    :: Lid Raw -> Renamed -> R (Lid Renamed)
addMod     :: Uid Raw -> R a -> R (Uid Renamed, a)

addVal = bindVar

addType l i = do
  let l' = Lid i (unLid l)
  tell (MdTycon l l')
  return l'

addMod u body = do
  let u' = uid (unUid u)
  (a, md) <- steal body
  tell (MdModule u u' md)
  return (u', a)


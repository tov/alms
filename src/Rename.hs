{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      QuasiQuotes,
      RankNTypes,
      RelaxedPolyRec,
      TemplateHaskell,
      TypeSynonymInstances #-}
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
  -- * REPL query
  getRenamingInfo, RenamingInfo(..),
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
import Control.Monad.Error as M.E

-- | The type to save the state of the renamer between calls
data RenameState = RenameState {
  savedEnv     :: Env,
  savedCounter :: Renamed
} deriving Show

-- | The initial state
renameState0 :: RenameState
renameState0  = RenameState {
  savedEnv      = mempty {
    datacons = M.singleton (uid "()") (uid "()", mkBogus "built-in", ())
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

instance MonadError String Renaming where
  throwError = fail
  catchError body handler =
    R (catchError (unR body) (unR . handler))

-- | The renaming environment
data Env = Env {
  tycons, vars    :: !(EnvMap Lid    ()),
  datacons        :: !(EnvMap Uid    ()),
  modules, sigs   :: !(EnvMap Uid    (Module, Env)),
  tyvars          :: !(EnvMap TyVar  Bool)
} deriving Show

type EnvMap f i = M.Map (f Raw) (f Renamed, Loc, i)

-- | A module item is one of 5 renaming entries, an empty module, r
--   a pair of modules.  Note that while type variables are not actual
--   module items, they are exported from patterns, so it's useful to
--   have them here.
data Module
  = MdNil
  | MdApp     !Module !Module
  | MdTycon   !Loc !(Lid Raw)   !(Lid Renamed)
  | MdVar     !Loc !(Lid Raw)   !(Lid Renamed)
  | MdDatacon !Loc !(Uid Raw)   !(Uid Renamed)
  | MdModule  !Loc !(Uid Raw)   !(Uid Renamed) !Module
  | MdSig     !Loc !(Uid Raw)   !(Uid Renamed) !Module
  | MdTyvar   !Loc !(TyVar Raw) !(TyVar Renamed)
  deriving Show

-- | The renaming context, which includes the environment (which is
--   persistant), and other information with is not
data Context = Context {
  env      :: !Env,
  allocate :: !Bool,
  location :: !Loc
}

-- | Run a renaming computation
runRenaming :: Bool -> Loc -> RenameState -> Renaming a ->
               Either String (a, RenameState)
runRenaming nonTrivial loc saved action = do
  (result, counter, md) <-
    runRWST (unR action)
      Context {
        env      = savedEnv saved,
        allocate = nonTrivial,
        location = loc
      }
      (savedCounter saved)
  let env' = savedEnv saved `mappend` envify md
  return (result, RenameState env' counter)

-- | Run a renaming computation
runRenamingM :: Monad m =>
                Bool -> Loc -> RenameState -> Renaming a -> m (a, RenameState)
runRenamingM  = either fail return <$$$$> runRenaming

-- | Alias
type R a  = Renaming a

instance Monoid Env where
  mempty = Env M.empty M.empty M.empty M.empty M.empty M.empty
  mappend (Env a1 a2 a3 a4 a5 a6) (Env b1 b2 b3 b4 b5 b6) =
    Env (a1 & b1) (a2 & b2) (a3 & b3) (a4 & b4) (a5 & b5) (a6 & b6)
      where a & b = M.union b a

instance Monoid Module where
  mempty  = MdNil
  mappend = MdApp

-- | Open a module into an environment
envify :: Module -> Env
envify MdNil            = mempty
envify (MdApp md1 md2)  = envify md1 `mappend` envify md2
envify (MdTycon loc l l')
  = mempty { tycons = M.singleton l (l', loc, ()) }
envify (MdVar loc l l')
  = mempty { vars = M.singleton l (l', loc, ()) }
envify (MdDatacon loc u u')
  = mempty { datacons = M.singleton u (u', loc, ()) }
envify (MdModule loc u u' md)
  = mempty { modules = M.singleton u (u',loc,(md,envify md)) }
envify (MdSig loc u u' md)
  = mempty { sigs = M.singleton u (u',loc,(md,envify md)) }
envify (MdTyvar loc tv tv')
  = mempty { tyvars = M.singleton tv (tv',loc,True) }

-- | Like 'asks', but in the 'R' monad
withContext :: (Context -> R a) -> R a
withContext  = R . (ask >>=) . fmap unR

-- | Run in the context of a given source location
withLoc :: Locatable loc => loc -> R a -> R a
withLoc loc =
  R . local (\cxt -> cxt { location = location cxt <<@ loc }) .  unR

-- | Append a module to the current environment
inModule :: Module -> R a -> R a
inModule m = local (\e -> e `mappend` envify m)

-- | Temporarily stop allocating unique ids
don'tAllocate :: R a -> R a
don'tAllocate = R . local (\cxt -> cxt { allocate = False }) . unR

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

-- | Get all the variable names, included qualified, bound in a module
getAllVariables :: Module -> [QLid Renamed]
getAllVariables = S.toList . loop where
  loop (MdApp md1 md2)      = loop md1 `S.union` loop md2
  loop (MdVar _ _ l')       = S.singleton (J [] l')
  loop (MdModule _ _ u' md) = S.mapMonotonic (\(J us l) -> J (u':us) l)
                                             (loop md)
  loop _                    = S.empty

-- | Temporarily hide the type variables in scope, and pass the
--   continuation a function to bring them back
hideTyvars :: R a -> R a
hideTyvars  = local (\e -> e { tyvars = M.map each (tyvars e) })
  where each (tv, loc, _) = (tv, loc, False)

-- | Look up something in an environment
envLookup :: (Ord k, Show k) =>
             (Env -> M.Map k k') ->
             Path (Uid Raw) k ->
             Env ->
             Either (Maybe (Path (Uid Renamed) (Uid Raw)))
                    (Path (Uid Renamed) k')
envLookup prj = loop [] where
  loop ms' (J []     x) e = case M.lookup x (prj e) of
    Just x' -> Right (J (reverse ms') x')
    Nothing -> Left Nothing
  loop ms' (J (m:ms) x) e = case M.lookup m (modules e) of
    Just (m', _, (_, e')) -> loop (m':ms') (J ms x) e'
    Nothing               -> Left (Just (J (reverse ms') m))

-- | Look up something in the environment
getGenericFull :: (Ord k, Show k) =>
              String -> (Env -> M.Map k k') ->
              Path (Uid Raw) k -> R (Path (Uid Renamed) k')
getGenericFull what prj qx = do
  e <- ask
  case envLookup prj qx e of
    Right qx'     -> return qx'
    Left Nothing  -> unbound what qx
    Left (Just m) -> unbound "module" m

-- | Look up something in the environment
getGeneric :: (Ord (f Raw), Show (f Raw)) =>
              String -> (Env -> EnvMap f i) ->
              Path (Uid Raw) (f Raw) -> R (Path (Uid Renamed) (f Renamed))
getGeneric = liftM (fmap (\(qx', _, _) -> qx')) <$$$> getGenericFull

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
getModule  = liftM pull . getGenericFull "structure" modules
  where
    pull (J ps (qu, _, (m, e))) = (J ps qu, m, e)

-- | Look up a module in the environment
getSig :: QUid Raw -> R (QUid Renamed, Module, Env)
getSig  = liftM pull . getGenericFull "signature" sigs
  where
    pull (J ps (qu, _, (m, e))) = (J ps qu, m, e)

-- | Look up a variable in the environment
getTyvar :: TyVar Raw -> R (TyVar Renamed)
getTyvar tv = do
  e <- asks tyvars
  case M.lookup tv e of
    Nothing              -> fail $ "type variable not in scope: " ++ show tv
    Just (tv', _, True)  -> return tv'
    Just (_, loc, False) -> fail $
      "type variable not in scope: " ++ show tv ++ "\n" ++
      "NB: It was bound at " ++ show loc ++ " but nested declarations\n" ++
      "cannot see tyvars from their parent expression."

-- | Get a new name for a variable binding
bindGeneric :: (Ord ident, Show ident, Antible ident) =>
               (Renamed -> ident -> ident') ->
               (Loc -> ident -> ident' -> Module) ->
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
  loc <- asks location
  tell (build loc x x')
  return x'

-- | Get a new name for a variable binding
bindVar :: Lid Raw -> R (Lid Renamed)
bindVar  = bindGeneric (\r -> Lid r . unLid) MdVar

-- | Get a new name for a variable binding
bindTycon :: Lid Raw -> R (Lid Renamed)
bindTycon  = bindGeneric (\r -> Lid r . unLid) MdTycon

-- | Get a new name for a data constructor binding
bindDatacon :: Uid Raw -> R (Uid Renamed)
bindDatacon = bindGeneric (\r -> Uid r . unUid) MdDatacon

-- | Get a new name for a module, and bind it in the environment
bindModule :: Uid Raw -> Module -> R (Uid Renamed)
bindModule u0 md = bindGeneric (\r -> Uid r . unUid) build u0
  where build loc old new = MdModule loc old new md

-- | Get a new name for a signature, and bind it in the environment
bindSig :: Uid Raw -> Module -> R (Uid Renamed)
bindSig u0 md = bindGeneric (\r -> Uid r . unUid) build u0
  where build loc old new = MdSig loc old new md

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
renameDecl d0 = withLoc d0 $ case d0 of
  [$dc| let $x : $opt:mt = $e |] -> do
    x'  <- renamePatt x
    mt' <- gmapM renameType mt
    e'  <- renameExpr e
    return [$dc|+ let $x' : $opt:mt' = $e' |]
  [$dc| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [$dc|+ type $list:tds' |]
  [$dc| abstype $list:ats with $list:ds end |] -> do
    let bindEach [$atQ| $anti:a |] = $antifail
        bindEach (N _ (AbsTy _ _ [$tdQ| $anti:a |])) = $antifail
        bindEach (N note at) = withLoc note $ do
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
  [$dc| module type $uid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [$dc|+ module type $uid:u' = $se1' |]
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

renameTyDecs :: [TyDec Raw] -> R [TyDec Renamed]
renameTyDecs tds = do
  let bindEach [$tdQ| $anti:a |] = $antifail
      bindEach (N note td)       = withLoc note $ do
        bindTycon (tdName td)
        return (tdName td, getLoc note)
  (llocs, md) <- listen $ mapM bindEach tds
  case unique fst llocs of
    Nothing -> return ()
    Just ((l, loc1), (_, loc2)) -> fail $
      "type `" ++ show l ++ "' declared twice in type group at " ++
      show loc1 ++ " and " ++ show loc2
  inModule md $ mapM (liftM snd . renameTyDec Nothing) tds

renameTyDec :: Maybe (QExp Raw) -> TyDec Raw ->
               R (Maybe (QExp Renamed), TyDec Renamed)
renameTyDec _   (N _ (TdAnti a)) = $antierror
renameTyDec mqe (N note (TdSyn l clauses)) = withLoc note $ do
  case mqe of
    Nothing -> return ()
    Just _  -> fail "BUG! can't rename QExp in context of type synonym"
  J [] l' <- getTycon (J [] l)
  clauses' <- forM clauses $ \(ps, rhs) -> withLoc ps $ do
    (ps', md) <- steal $ renameTyPats ps
    rhs' <- inModule md $ renameType rhs
    return (ps', rhs')
  return (Nothing, tdSyn l' clauses' <<@ note)
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
      TdSyn _ _ -> fail "BUG! can't happen in Rename.renameTyDec"
      TdDat _ _ cons -> do
        case unique fst cons of
          Nothing -> return ()
          Just ((u, _), (_, _)) -> fail $
            "repeated constructor `" ++ show u ++ "' in type declaration"
        cons' <- forM cons $ \(u, mt) -> withLoc mt $ do
          u'    <- bindDatacon u
          mt'   <- gmapM renameType mt
          return (u', mt')
        return (tdDat l' tvs' cons')
      TdAnti a -> $antifail
    return (mqe', td' <<@ note)

renameModExp :: ModExp Raw -> R (ModExp Renamed)
renameModExp me0 = withLoc me0 $ case me0 of
  [$me| struct $list:ds end |] -> do
    ds' <- renameDecls ds
    return [$me|+ struct $list:ds' end |]
  [$me| $quid:qu $list:_ |] -> do
    (qu', md, _) <- getModule qu
    let qls = getAllVariables md
    tell md
    return [$me|+ $quid:qu' $list:qls |]
  [$me| $me1 : $se2 |] -> do
    (me1', md1) <- steal $ renameModExp me1
    (se2', md2) <- steal $ renameSigExp se2
    undefined
  [$me| $anti:a |] -> $antifail

renameSigExp :: SigExp Raw -> R (SigExp Renamed)
renameSigExp se0 = withLoc se0 $ case se0 of
  [$seQ| sig $list:sgs end |] -> do
    (sgs', md) <- listen $ don'tAllocate $ renameMapM renameSigItem sgs
    inModule mempty $ checkSigDuplicates md
    return [$seQ|+ sig $list:sgs' end |]
  [$seQ| $quid:qu $list:_ |] -> do
    (qu', md, _) <- getSig qu
    let qls = getAllVariables md
    tell md
    return [$seQ|+ $quid:qu' $list:qls |]
  [$seQ| $se1 with type $list:tvs $qlid:ql = $t |] -> do
    (se1', md) <- listen $ renameSigExp se1
    ql' <- local (const mempty) $ inModule md $ getTycon ql
    case unique id tvs of
      Nothing      -> return ()
      Just (tv, _) -> fail $
        "type variable `" ++ show tv ++ "' bound twice in `with type'"
    (tvs', mdtvs) <- steal $ mapM bindTyvar tvs
    t' <- inModule mdtvs $ renameType t
    return [$seQ|+ $se1' with type $list:tvs' $qlid:ql' = $t' |]
  [$seQ| $anti:a |] -> $antifail

checkSigDuplicates :: Module -> R ()
checkSigDuplicates md = case md of
    MdNil                -> return ()
    MdApp md1 md2        -> do
      checkSigDuplicates md1
      inModule md1 $ checkSigDuplicates md2
    MdTycon   loc l  _   -> mustFail loc "type"        l $ getTycon (J [] l)
    MdVar     loc l  _   -> mustFail loc "variable"    l $ getVar (J [] l)
    MdDatacon loc u  _   -> mustFail loc "constructor" u $ getDatacon (J [] u)
    MdModule  loc u  _ _ -> mustFail loc "structure"   u $ getModule (J [] u)
    MdSig     loc u  _ _ -> mustFail loc "signature"   u $ getSig (J [] u)
    MdTyvar   loc tv _   -> mustFail loc "tyvar"      tv $ getTyvar tv
  where
    mustFail loc kind which check = do
      failed <- (False <$ check) `M.E.catchError` \_ -> return True
      unless failed $ do
        withLoc loc $
          fail $
            "signature contains repeated " ++ kind ++
            " `" ++ show which ++ "'"

-- | Rename a signature item and return the environment
--   that they bind
renameSigItem :: SigItem Raw -> R (SigItem Renamed)
renameSigItem sg0 = case sg0 of
  [$sgQ| val $lid:l : $t |] -> do
    l' <- bindVar l
    t' <- renameType t
    return [$sgQ|+ val $lid:l' : $t' |]
  [$sgQ| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [$sgQ|+ type $list:tds' |]
  [$sgQ| module $uid:u : $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindModule u md
    return [$sgQ|+ module $uid:u' : $se1' |]
  [$sgQ| module type $uid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [$sgQ|+ module type $uid:u' = $se1' |]
  [$sgQ| include $se1 |] -> do
    se1' <- renameSigExp se1
    return [$sgQ|+ include $se1' |]
  [$sgQ| exception $uid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- gmapM renameType mt
    return [$sgQ|+ exception $uid:u' of $opt:mt' |]
  [$sgQ| $anti:a |] -> $antifail

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
  let bindEach rest (l,x,t,e) = withLoc l $ do
        x' <- bindVar x
        return ((l,x',t,e):rest)
  (lxtes', md) <- steal $ foldM bindEach [] lxtes
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

-- | Rename a type pattern
renameTyPats :: [TyPat Raw] -> R [TyPat Renamed]
renameTyPats x00 =
  withLoc x00 $
    M.S.evalStateT (mapM loop x00) M.empty where
  loop :: TyPat Raw ->
          M.S.StateT (M.Map (TyVar Raw) Loc) Renaming (TyPat Renamed)
  loop x0 = case x0 of
    [$tpQ| $antiP:a |] -> $antifail
    N note (TpVar tv var) -> do
      tv' <- tyvar (getLoc note) tv
      return (tpVar tv' var <<@ note)
    [$tpQ| ($list:tps) $qlid:ql |] -> do
      ql'  <- lift (withLoc _loc (getTycon ql))
      tps' <- mapM loop tps
      return [$tpQ|+ ($list:tps') $qlid:ql' |]
  --
  tyvar :: Loc -> TyVar Raw ->
           M.S.StateT (M.Map (TyVar Raw) Loc) Renaming (TyVar Renamed)
  tyvar loc1 tv = do
    seen <- M.S.get
    case M.lookup tv seen of
      Just loc2 -> fail $
        "type variable " ++ show tv ++ " bound twice in type pattern at " ++
        show loc1 ++ " and " ++ show loc2
      Nothing   -> do
        M.S.put (M.insert tv loc1 seen)
        lift (bindTyvar tv)

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

-- | Rename a pattern
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
        M.S.lift (withLoc loc1 (bindVar l))
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
  loc <- R $ asks location
  tell (MdTycon loc l l')
  return l'

addMod u body = do
  let u' = uid (unUid u)
  (a, md) <- steal body
  loc <- R $ asks location
  tell (MdModule loc u u' md)
  return (u', a)

-- | Result for 'getRenamingInfo'
data RenamingInfo
  = ModuleAt   { renInfoLoc :: Loc, renInfoQUid :: QUid Renamed }
  | VariableAt { renInfoLoc :: Loc, renInfoQLid :: QLid Renamed }
  | TyconAt    { renInfoLoc :: Loc, renInfoQLid :: QLid Renamed }
  | DataconAt  { renInfoLoc :: Loc, renInfoQUid :: QUid Renamed }
  deriving Show

-- | For the REPL to find out where identifiers are bound and their
--   renamed name for looking up type info
getRenamingInfo :: Ident Raw -> RenameState -> [RenamingInfo]
getRenamingInfo ident RenameState { savedEnv = e } =
  catMaybes $ case view ident of
    Left ql  -> [ look tycons ql TyconAt, look vars ql VariableAt ]
    Right qu -> [ look modules qu ModuleAt, look datacons qu DataconAt ]
  where
    look prj qx build = case envLookup prj qx e of
      Left _                    -> Nothing
      Right (J ps (x', loc, _)) -> Just (build loc (J ps x'))


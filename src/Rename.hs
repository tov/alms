{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      PatternGuards,
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
  renamingEnterScope,
) where

import ErrorMessage

import Meta.Quasi
import Syntax hiding ((&))
import Data.Loc
import TypeAnnotation
import qualified Syntax.Decl
import qualified Syntax.Expr
import qualified Syntax.Notable
import qualified Syntax.Patt
import Util
import Ppr (Ppr(..))

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S

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

-- | Generate a renamer error.
renameError :: Message V -> R a
renameError msg0 = do
  loc <- R (asks location)
  throwAlms (AlmsException RenamerPhase loc msg0)

renameBug :: String -> String -> R a
renameBug culprit msg0 = do
  loc <- R (asks location)
  throwAlms (almsBug RenamerPhase loc culprit msg0)

-- | The renaming monad: Reads a context, writes a module, and
--   keeps track of a renaming counter state.
newtype Renaming a = R {
  unR :: RWST Context Module RState (Either AlmsException) a
} deriving Functor

-- | The threaded state of the renamer.
newtype RState = RState {
  -- | The gensym counter:
  rsCounter :: Renamed
}

instance Monad Renaming where
  return  = R . return
  m >>= k = R (unR m >>= unR . k)
  fail    = renameError . [msg| $words:1 |]

instance Applicative Renaming where
  pure  = return
  (<*>) = ap

instance MonadWriter Module Renaming where
  listen = R . listen . unR
  tell   = R . tell
  pass   = R . pass . unR

instance MonadReader Env Renaming where
  ask     = R (asks env)
  local f = R . local (\cxt -> cxt { env = f (env cxt) }) . unR

instance MonadError AlmsException Renaming where
  throwError = R . throwError
  catchError body handler =
    R (catchError (unR body) (unR . handler))

instance MonadAlmsError Renaming where
  throwAlms = throwError
  catchAlms = catchError

-- | The renaming environment
data Env = Env {
  tycons, vars    :: !(EnvMap Lid    ()),
  datacons        :: !(EnvMap Uid    ()),
  modules, sigs   :: !(EnvMap Uid    (Module, Env)),
  tyvars          :: !(EnvMap Lid    (QLit, Bool))
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
  location :: !Loc,
  inExpr   :: !Bool
}

-- | Run a renaming computation
runRenaming :: Bool -> Loc -> RenameState -> Renaming a ->
               Either AlmsException (a, RenameState)
runRenaming nonTrivial loc saved action = do
  (result, rstate, md) <-
    runRWST (unR action)
      Context {
        env      = savedEnv saved,
        allocate = nonTrivial,
        location = loc,
        inExpr   = False
      }
      RState {
        rsCounter = savedCounter saved
      }
  let env' = savedEnv saved `mappend` envify md
  return (result, RenameState env' (rsCounter rstate))

-- | Run a renaming computation
runRenamingM :: MonadAlmsError m =>
                Bool -> Loc -> RenameState -> Renaming a ->
                m (a, RenameState)
runRenamingM = unTryAlms . return <$$$$> runRenaming

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
  = mempty { tyvars = M.singleton (tvname tv)
                                  (tvname tv',loc,(tvqual tv', True)) }

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

-- | Run in the environment consisting of only the given module
onlyInModule :: Module -> R a -> R a
onlyInModule = local (const mempty) <$$> inModule

-- | Add the free annotation type variables in the given syntax
--   for the context of the action.
withAnnotationTVs :: HasAnnotations s Raw => s -> R a -> R a
withAnnotationTVs stx action = do
  ((), md) <- steal $ traverse_ bindTyvar (annotFtvSet stx)
  inModule md action

-- | Hide any annotation type variables that were in scope.
hideAnnotationTVs :: R a -> R a
hideAnnotationTVs = local (\e -> e { tyvars = each <$> tyvars e })
  where each (a, b, (c, _)) = (a, b, (c, False))

-- | Temporarily stop allocating unique ids
don'tAllocate :: R a -> R a
don'tAllocate = R . local (\cxt -> cxt { allocate = False }) . unR

-- | Generate an unbound name error
unbound :: Ppr a => String -> a -> R b
unbound ns a =
  renameError [msg| $words:ns not in scope: $q:a |]

-- | Generate an error about a name declared twice
repeatedMsg :: Ppr a => String -> a -> String -> [Loc] -> Message V
repeatedMsg what a inwhat locs =
  [msg|
    $words:what $a
    repeated $words:times in $words:inwhat $words:at
    $ul:slocs
  |]
  where
    times = case length locs of
      0 -> ""
      1 -> ""
      2 -> "twice"
      3 -> "thrice"
      _ -> show (length locs) ++ " times"
    at    = if length locs > 1 then "at:" else ""
    slocs = map [msg| $show:1 |] locs

-- | Generate an error about a name declared twice
repeated :: Ppr a => String -> a -> String -> [Loc] -> R b
repeated what a inwhat locs =
  renameError $ repeatedMsg what [msg| $q:a |] inwhat locs

-- | Generate an error about a name declared twice
repeatedTVs :: [TyVar i] -> String -> R b
repeatedTVs []  _             = renameBug "repatedTVs" "got empty list"
repeatedTVs tvs@(tv:_) inwhat =
  let quals  = ordNub (tvqual <$> tvs)
      name   = tvname tv
      bothQs = length quals > 1
      callIt = if bothQs then [msg| `$name / '$name |] else [msg| $tv |]
      msg0   = repeatedMsg "Type variable" callIt inwhat (getLoc <$> tvs)
   in renameError $
        if bothQs
          then [msg|
                  $msg0
                  <indent>
                    (Type variables with the same name but different
                    qualifiers may not appear in the same scope.)
                  </indent>
                |]
          else msg0

-- | Are all keys of the list unique?  If not, return the key and
--   list of two or more values with the same keys
unique       :: Ord a => (b -> a) -> [b] -> Maybe (a, [b])
unique getKey = loop M.empty where
  loop _    []     = Nothing
  loop seen (x:xs) =
    let k = getKey x
     in case M.lookup k seen of
          Nothing -> loop (M.insert k x seen) xs
          Just x' -> Just (k, x' : x : filter ((== k) . getKey) xs)

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
    Left (Just m) -> unbound "Module" m

-- | Look up something in the environment
getGeneric :: (Ord (f Raw), Show (f Raw)) =>
              String -> (Env -> EnvMap f i) ->
              Path (Uid Raw) (f Raw) -> R (Path (Uid Renamed) (f Renamed))
getGeneric = liftM (fmap (\(qx', _, _) -> qx')) <$$$> getGenericFull

-- | Look up a variable in the environment
getVar :: QLid Raw -> R (QLid Renamed)
getVar  = getGeneric "Variable" vars

-- | Look up a data constructor in the environment
getDatacon :: QUid Raw -> R (QUid Renamed)
getDatacon  = getGeneric "Data constructor" datacons

-- | Look up a variable in the environment
getTycon :: QLid Raw -> R (QLid Renamed)
getTycon  = getGeneric "Type constructor" tycons

-- | Look up a module in the environment
getModule :: QUid Raw -> R (QUid Renamed, Module, Env)
getModule  = liftM pull . getGenericFull "Structure" modules
  where
    pull (J ps (qu, _, (m, e))) = (J ps qu, m, e)

-- | Look up a module in the environment
getSig :: QUid Raw -> R (QUid Renamed, Module, Env)
getSig  = liftM pull . getGenericFull "Signature" sigs
  where
    pull (J ps (qu, _, (m, e))) = (J ps qu, m, e)

-- | Look up a type variable in the environment. This is complicated,
--   because there are several possibilities.
getTyvar :: TyVar Raw -> R (TyVar Renamed)
getTyvar tv@(TV name ql _) = do
  e <- asks tyvars
  case M.lookup name e of
    -- If the type variable isn't found in the block-structured type
    -- variable environment, that is an error.
    Nothing                          -> do
      renameError [msg| Type variable $tv is not in scope. |]
    --
    -- If the type variable *is* found in the bound type variable
    -- environment, we need to check if it's in the current scope or
    -- hidden, and if it's in the current scope, whether the qualifier
    -- matches.  If the qualifier doesn't match or if it's hidden, that
    -- is an error.
    Just (name', loc', (ql', True))
      | ql == ql'                    -> return (TV name' ql' loc')
      | otherwise                    ->
      renameError $
        [msg|
          Type variable $tv is not in scope.
          <indent>
             (Type variable $1 was bound at $loc', but the same
             type variable name may not occur with different qualifiers
             in the same scope.)
          </indent>
        |] (TV name' ql' loc')
    --
    Just (_,     loc', (_,   False)) -> do
      renameError
        [msg|
          Type variable $tv is not in scope.
          <indent>
             (It was bound at $loc', but a nested declaration
              can neither see nor shadow type variables from its
              parent expression.)
          </indent>
        |]
getTyvar (TVAnti a) = $antifail

-- | Get a new name for a variable binding
bindGeneric :: (Ord ident, Show ident, Antible ident) =>
               (Renamed -> ident -> ident') ->
               (Loc -> ident -> ident' -> Module) ->
               ident -> R ident'
bindGeneric ren build x = do
  case prjAnti x of
    Just a  -> $antifail
    Nothing -> return ()
  new <- newRenamed
  loc <- R (asks location)
  let x' = ren new x
  tell (build loc x x')
  return x'

-- | Allocate a new 'Renamed' token if we're in the right mode.
newRenamed :: R Renamed
newRenamed = R $ do
  doAlloc <- asks allocate
  if doAlloc
    then do
      rstate  <- get
      put rstate { rsCounter = succ (rsCounter rstate) }
      return (rsCounter rstate)
    else do
      return trivialId

-- | Get a new name for a variable binding
bindVar :: Lid Raw -> R (Lid Renamed)
bindVar  = bindGeneric renLid MdVar

-- | Get a new name for a variable binding
bindTycon :: Lid Raw -> R (Lid Renamed)
bindTycon  = bindGeneric renLid MdTycon

-- | Get a new name for a data constructor binding
bindDatacon :: Uid Raw -> R (Uid Renamed)
bindDatacon = bindGeneric renUid MdDatacon

-- | Get a new name for a module, and bind it in the environment
bindModule :: Uid Raw -> Module -> R (Uid Renamed)
bindModule u0 md = bindGeneric renUid build u0
  where build loc old new = MdModule loc old new md

-- | Get a new name for a signature, and bind it in the environment
bindSig :: Uid Raw -> Module -> R (Uid Renamed)
bindSig u0 md = bindGeneric renUid build u0
  where build loc old new = MdSig loc old new md

-- | Add a type variable to the scope
bindTyvar :: TyVar Raw -> R (TyVar Renamed)
bindTyvar tv = do
  e <- asks tyvars
  case M.lookup (tvname tv) e of
    Nothing                         -> bindGeneric insert MdTyvar tv
    Just (name', loc', (ql', _)) ->
      if tvqual tv == ql'
        then
          renameError $
            [msg|
              Cannot shadow type variable $tv; it is already
              bound at $loc'.
            |]
        else
          renameError $
            [msg|
              Cannot introduce type variable $tv, because $1 is
              already bound at $loc'.  The same type variable name cannot
              appear in the same scope with different qualifiers.
            |] (TV name' ql' loc')
  where insert r (TV l q loc) = TV (renLid r l) q loc
        insert _ (TVAnti a)   = antierror "bindTyvar" a

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
renameProg [prQ| $list:ds in $opt:me1 |] = do
  (ds', md) <- listen $ renameDecls ds
  me1' <- inModule md $ traverse renameExpr me1
  return [prQ|+ $list:ds' in $opt:me1' |]

-- | Rename a list of declarations and return the environment
--   that they bind
renameDecls :: [Decl Raw] -> R [Decl Renamed]
renameDecls  = renameMapM renameDecl

-- | Rename a declaration and return the environment that it binds
renameDecl :: Decl Raw -> R (Decl Renamed)
renameDecl d0 = withLoc d0 $ case d0 of
  [dc| let $x = $e |] -> do
    x'  <- renamePatt x
    e'  <- renameExpr e
    return [dc|+ let $x' = $e' |]
  [dc| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [dc|+ type $list:tds' |]
  [dc| abstype $list:ats with $list:ds end |] -> do
    let bindEach [atQ| $anti:a |] = $antifail
        bindEach (N _ (AbsTy _ _ [tdQ| $anti:a |])) = $antifail
        bindEach (N note at) = withLoc note $ do
          let l = tdName (dataOf (atdecl at))
          bindTycon l
          return (l, getLoc note)
    (llocs, mdT) <- listen $ mapM bindEach ats
    case unique fst llocs of
      Nothing -> return ()
      Just (l, locs) ->
        repeated "Type declaration for" l "abstype group" (snd <$> locs)
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
    return [dc|+ abstype $list:ats' with $list:ds' end |]
  [dc| module INTERNALS = $me1 |] ->
    R $ local (\context -> context { allocate = False }) $ unR $ do
      let u = uid "INTERNALS"
      (me1', md) <- steal $ renameModExp me1
      u' <- bindModule u md
      return [dc|+ module $uid:u' = $me1' |]
  [dc| module $uid:u = $me1 |] -> do
    (me1', md) <- steal $ renameModExp me1
    u' <- bindModule u md
    return [dc|+ module $uid:u' = $me1' |]
  [dc| module type $uid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [dc|+ module type $uid:u' = $se1' |]
  [dc| open $me1 |] -> do
    me1' <- renameModExp me1
    return [dc|+ open $me1' |]
  [dc| local $list:ds1 with $list:ds2 end |] -> do
    (ds1', md) <- steal $ renameDecls ds1
    ds2' <- inModule md $ renameDecls ds2
    return [dc| local $list:ds1' with $list:ds2' end |]
  [dc| exception $uid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- traverse renameType mt
    return [dc|+ exception $uid:u' of $opt:mt' |]
  [dc| $anti:a |] -> $antifail
    {-
  -}

renameTyDecs :: [TyDec Raw] -> R [TyDec Renamed]
renameTyDecs tds = do
  let bindEach [tdQ| $anti:a |] = $antifail
      bindEach (N note td)       = withLoc note $ do
        bindTycon (tdName td)
        return (tdName td, getLoc note)
  (llocs, md) <- listen $ mapM bindEach tds
  case unique fst llocs of
    Nothing -> return ()
    Just (l, locs) ->
      repeated "Type declaration for" l "type group" (snd <$> locs)
  inModule md $ mapM (liftM snd . renameTyDec Nothing) tds

renameTyDec :: Maybe (QExp Raw) -> TyDec Raw ->
               R (Maybe (QExp Renamed), TyDec Renamed)
renameTyDec _   (N _ (TdAnti a)) = $antierror
renameTyDec mqe (N note (TdSyn l clauses)) = withLoc note $ do
  case mqe of
    Nothing -> return ()
    Just _  ->
      renameBug "renameTyDec" "can’t rename QExp in context of type synonym"
  J [] l' <- getTycon (J [] l)
  clauses' <- forM clauses $ \(ps, rhs) -> withLoc ps $ do
    (ps', md) <- steal $ renameTyPats ps
    rhs' <- inModule md $ renameType rhs
    return (ps', rhs')
  return (Nothing, tdSyn l' clauses' <<@ note)
renameTyDec mqe (N note td)      = withLoc note $ do
  J [] l' <- getTycon (J [] (tdName td))
  let tvs = tdParams td
  case unique tvname tvs of
    Nothing        -> return ()
    Just (_, tvs') -> repeatedTVs tvs' "type parameters"
  (tvs', mdTvs) <- steal $ mapM bindTyvar tvs
  inModule mdTvs $ do
    mqe' <- traverse renameQExp mqe
    td'  <- case td of
      TdAbs _ _ variances gs qe -> do
        qe' <- renameQExp qe
        gs' <- ordNub <$> mapM getTyvar gs
        return (tdAbs l' tvs' variances gs' qe')
      TdSyn _ _ -> renameBug "renameTyDec" "unexpected TdSyn"
      TdDat _ _ cons -> do
        case unique fst cons of
          Nothing -> return ()
          Just (u, _) ->
            repeated "Data constructor" u "type declaration" []
        cons' <- forM cons $ \(u, mt) -> withLoc mt $ do
          let u' = uid (unUid u)
          tell (MdDatacon (getLoc mt) u u')
          mt'   <- traverse renameType mt
          return (u', mt')
        return (tdDat l' tvs' cons')
      TdAnti a -> $antifail
    return (mqe', td' <<@ note)

renameModExp :: ModExp Raw -> R (ModExp Renamed)
renameModExp me0 = withLoc me0 $ case me0 of
  [me| struct $list:ds end |] -> do
    ds' <- renameDecls ds
    return [me|+ struct $list:ds' end |]
  [me| $quid:qu $list:_ |] -> do
    (qu', md, _) <- getModule qu
    let qls = getAllVariables md
    tell md
    return [me|+ $quid:qu' $list:qls |]
  [me| $me1 : $se2 |] -> do
    (me1', md1) <- steal $ renameModExp me1
    (se2', md2) <- steal $ renameSigExp se2
    onlyInModule md1 $ sealWith md2
    return [me| $me1' : $se2' |]
  [me| $anti:a |] -> $antifail

renameSigExp :: SigExp Raw -> R (SigExp Renamed)
renameSigExp se0 = withLoc se0 $ case se0 of
  [seQ| sig $list:sgs end |] -> do
    (sgs', md) <- listen $ don'tAllocate $ renameMapM renameSigItem sgs
    onlyInModule mempty $ checkSigDuplicates md
    return [seQ|+ sig $list:sgs' end |]
  [seQ| $quid:qu $list:_ |] -> do
    (qu', md, _) <- getSig qu
    let qls = getAllVariables md
    tell md
    return [seQ|+ $quid:qu' $list:qls |]
  [seQ| $se1 with type $list:tvs $qlid:ql = $t |] -> do
    (se1', md) <- listen $ renameSigExp se1
    ql' <- onlyInModule md $ getTycon ql
    case unique id tvs of
      Nothing      -> return ()
      Just (_, tvs') -> repeatedTVs tvs' "with-type"
    (tvs', mdtvs) <- steal $ mapM bindTyvar tvs
    t' <- inModule mdtvs $ renameType t
    return [seQ|+ $se1' with type $list:tvs' $qlid:ql' = $t' |]
  [seQ| $anti:a |] -> $antifail

checkSigDuplicates :: Module -> R ()
checkSigDuplicates md = case md of
    MdNil                -> return ()
    MdApp md1 md2        -> do
      checkSigDuplicates md1
      inModule md1 $ checkSigDuplicates md2
    MdTycon   loc l  _   -> mustFail loc "Type"        l $ getTycon (J [] l)
    MdVar     loc l  _   -> mustFail loc "Variable"    l $ getVar (J [] l)
    MdDatacon loc u  _   -> mustFail loc "Constructor" u $ getDatacon (J [] u)
    MdModule  loc u  _ _ -> mustFail loc "Structure"   u $ getModule (J [] u)
    MdSig     loc u  _ _ -> mustFail loc "Signature"   u $ getSig (J [] u)
    MdTyvar   loc tv _   -> mustFail loc "Tyvar"      tv $ getTyvar tv
  where
    mustFail loc kind which check = do
      failed <- (False <$ check) `catchError` \_ -> return True
      unless failed $ do
        withLoc loc $
          repeated kind which "signature" []

sealWith :: Module -> R ()
sealWith = loop Nothing where
  loop b md = case md of
    MdNil              -> return ()
    MdApp md1 md2      -> do loop b md1; loop b md2
    MdTycon   _ l _   -> do
      (l', loc, _) <- locate b "type constructor" tycons l
      tell (MdTycon loc l l')
    MdVar     _ l _   -> do
      (l', loc, _) <- locate b "variable" vars l
      tell (MdVar loc l l')
    MdDatacon _ u _   -> do
      (u', loc, _) <- locate b "data constructor" datacons u
      tell (MdDatacon loc u u')
    MdModule  _ u _ md2 -> do
      (u', loc, (md1, _)) <- locate b "module" modules u
      ((), md1') <- steal $ onlyInModule md1 $ loop b md2
      tell (MdModule loc u u' md1')
    MdSig     _ u _ md2 -> do
      (u', loc, (md1, _)) <- locate b "module type" sigs u
      ((), _   ) <- steal $ onlyInModule md2 $ loop (Just (Left u)) md1
      ((), md1') <- steal $ onlyInModule md1 $ loop (Just (Right u)) md2
      tell (MdSig loc u u' md1')
    MdTyvar   _ _ _   ->
      renameBug "sealWith" "signature can’t declare type variable"
  locate b what prj ident = do
    m <- asks prj
    case M.lookup ident m of
      Just ident' -> return ident'
      Nothing     -> renameError $
        case b of
          Nothing -> [msg|
            In signature matching, structure is missing
            $words:what $q:ident,
            which is present in ascribed signature.
          |]
          Just (Left u) -> [msg|
            In exact signature matching (for nested signature $u)
            found unexpected $words:what $q:ident.
          |]
          Just (Right u) -> [msg|
            In exact signature matching (for nested signature $u)
            missing expected $words:what $q:ident.
          |]

-- | Rename a signature item and return the environment
--   that they bind
renameSigItem :: SigItem Raw -> R (SigItem Renamed)
renameSigItem sg0 = case sg0 of
  [sgQ| val $lid:l : $t |] -> do
    l' <- bindVar l
    t' <- renameType (closeType t)
    return [sgQ|+ val $lid:l' : $t' |]
  [sgQ| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [sgQ|+ type $list:tds' |]
  [sgQ| module $uid:u : $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindModule u md
    return [sgQ|+ module $uid:u' : $se1' |]
  [sgQ| module type $uid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [sgQ|+ module type $uid:u' = $se1' |]
  [sgQ| include $se1 |] -> do
    se1' <- renameSigExp se1
    return [sgQ|+ include $se1' |]
  [sgQ| exception $uid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- traverse renameType mt
    return [sgQ|+ exception $uid:u' of $opt:mt' |]
  [sgQ| $anti:a |] -> $antifail

-- | Rename an expression
renameExpr :: Expr Raw -> R (Expr Renamed)
renameExpr e00 = withLoc e00 . withAnnotationTVs e00 $ loop e00 where
  loop e0 = case e0 of
    [ex| $qlid:ql |] -> do
      ql' <- getVar ql
      return [ex|+ $qlid:ql' |]
    [ex| $lit:lit |] -> do
      lit' <- renameLit lit
      return [ex|+ $lit:lit' |]
    [ex| $quid:qu $opt:me |] -> do
      qu' <- getDatacon qu
      me' <- traverse loop me
      return [ex|+ $quid:qu' $opt:me' |]
    [ex| `$uid:u $opt:me |] -> do
      let u' = trivialRename u
      me' <- traverse loop me
      return [ex|+ `$uid:u' $opt:me' |]
    [ex| #$uid:u $e |] -> do
      let u' = trivialRename u
      e' <- loop e
      return [ex|+ #$uid:u' $e' |]
    [ex| let $x = $e1 in $e2 |] -> do
      (x', md) <- steal $ renamePatt x
      e1' <- loop e1
      e2' <- inModule md $ loop e2
      return [ex| let $x' = $e1' in $e2' |]
    [ex| match $e1 with $list:cas |] -> do
      e1'  <- loop e1
      cas' <- mapM renameCaseAlt cas
      return [ex|+ match $e1' with $list:cas' |]
    [ex| let rec $list:bns in $e |] -> do
      (bns', md) <- renameBindings bns
      e' <- inModule md $ loop e
      return [ex|+ let rec $list:bns' in $e' |]
    [ex| let $decl:d in $e |] -> do
      (d', md) <- steal . hideAnnotationTVs $ renameDecl d
      e' <- inModule md (loop e)
      return [ex|+ let $decl:d' in $e' |]
    [ex| ($e1, $e2) |] -> do
      e1' <- loop e1
      e2' <- loop e2
      return [ex|+ ($e1', $e2') |]
    [ex| fun $x -> $e |] -> do
      (x', md) <- steal $ renamePatt x
      e' <- inModule md $ loop e
      return [ex|+ fun $x' -> $e' |]
    [ex| $e1 $e2 |] -> do
      e1' <- loop e1
      e2' <- loop e2
      return [ex|+ $e1' $e2' |]
    [ex| ( $e : $t) |] -> do
      e'  <- loop e
      t'  <- renameType t
      return [ex| ( $e' : $t' ) |]
    [ex| ( $e :> $t) |] -> do
      e'  <- loop e
      t'  <- renameType t
      return [ex| ( $e' :> $t' ) |]
    [ex| $anti:a |] -> $antifail

-- | Rename a literal (no-op, except fails on antiquotes)
renameLit :: Lit -> R Lit
renameLit lit0 = case lit0 of
  LtAnti a -> $antifail
  _        -> return lit0

-- | Rename a case alternative
renameCaseAlt :: CaseAlt Raw -> R (CaseAlt Renamed)
renameCaseAlt ca0 = withLoc ca0 $ case ca0 of
  [caQ| $x -> $e |] -> do
    (x', md) <- steal $ renamePatt x
    e' <- inModule md $ renameExpr e
    return [caQ|+ $x' -> $e' |]
  [caQ| $antiC:a |] -> $antifail

-- | Rename a set of let rec bindings
renameBindings :: [Binding Raw] -> R ([Binding Renamed], Module)
renameBindings bns = do
  lxes <- forM bns $ \bn ->
    case bn of
      [bnQ| $lid:x = $e |] -> return (_loc, x, e)
      [bnQ| $antiB:a |] -> $antifail
  case unique (\(_,x,_) -> x) lxes of
    Nothing          -> return ()
    Just (x, locs) ->
      repeated "Variable binding for" x "let-rec" (sel1 <$> locs)
  let bindEach rest (l,x,e) = withLoc l $ do
        x' <- bindVar x
        return ((l,x',e):rest)
  (lxes', md) <- steal $ foldM bindEach [] lxes
  bns' <- inModule md $
            forM (reverse lxes') $ \(l,x',e) -> withLoc l $ do
              let _loc = l
              e'  <- renameExpr e
              return [bnQ|+ $lid:x' = $e' |]
  return (bns', md)

-- | Rename a type
renameType :: Type Raw -> R (Type Renamed)
renameType t0 = case t0 of
  [ty| ($list:ts) $qlid:ql |] -> do
    ql' <- getTycon ql
    ts' <- mapM renameType ts
    return [ty|+ ($list:ts') $qlid:ql' |]
  [ty| '$tv |] -> do
    tv' <- getTyvar tv
    return [ty|+ '$tv' |]
  [ty| $t1 -[$opt:mqe]> $t2 |] -> do
    t1'  <- renameType t1
    mqe' <- traverse renameQExp mqe
    t2'  <- renameType t2
    return [ty|+ $t1' -[$opt:mqe']> $t2' |]
  [ty| $quant:u '$tv. $t |] -> do
    (tv', md) <- steal $ bindTyvar tv
    t' <- inModule md $ renameType t
    return [ty|+ $quant:u '$tv'. $t' |]
  [ty| mu '$tv. $t |] -> do
    (tv', md) <- steal $ bindTyvar tv
    t' <- inModule md $ renameType t
    return [ty|+ mu '$tv'. $t' |]
  [ty| `$uid:u of $t1 | $t2 |] -> do
    let u' = trivialRename u
    t1' <- renameType t1
    t2' <- renameType t2
    return [ty| `$uid:u' of $t1' | $t2' |]
  [ty| $anti:a |] -> $antifail

-- | Rename a type pattern
renameTyPats :: [TyPat Raw] -> R [TyPat Renamed]
renameTyPats x00 =
  withLoc x00 $
    evalStateT (mapM loop x00) M.empty where
  loop :: TyPat Raw ->
          StateT (M.Map (Lid Raw) (TyVar Raw, Loc)) Renaming (TyPat Renamed)
  loop x0 = case x0 of
    [tpQ| $antiP:a |] -> $antifail
    N note (TpVar tv var) -> do
      tv' <- tyvar (getLoc note) tv
      return (tpVar tv' var <<@ note)
    N note (TpRow tv var) -> do
      tv' <- tyvar (getLoc note) tv
      return (tpRow tv' var <<@ note)
    [tpQ| ($list:tps) $qlid:ql |] -> do
      ql'  <- lift (withLoc _loc (getTycon ql))
      tps' <- mapM loop tps
      return [tpQ|+ ($list:tps') $qlid:ql' |]
  --
  tyvar :: Loc -> TyVar Raw ->
           StateT (M.Map (Lid Raw) (TyVar Raw, Loc)) Renaming (TyVar Renamed)
  tyvar loc1 tv = do
    seen <- get
    case M.lookup (tvname tv) seen of
      Just (tv', _) ->
        lift (repeatedTVs [tv,tv'] "type parameters")
      Nothing   -> do
        put (M.insert (tvname tv) (tv, loc1) seen)
        lift (bindTyvar tv)

-- | Rename a qualifier expression
renameQExp :: QExp Raw -> R (QExp Renamed)
renameQExp qe0 = case qe0 of
  [qeQ| $qlit:qlit |] -> do
    return [qeQ|+ $qlit:qlit |]
  [qeQ| $qvar:tv |] -> do
    tv' <- getTyvar tv
    return [qeQ| $qvar:tv' |]
  [qeQ| $qe1 \/ $qe2 |] -> do
    qe1' <- renameQExp qe1
    qe2' <- renameQExp qe2
    return [qeQ| $qe1' \/ $qe2' |]
  [qeQ| $anti:a |] -> do
    $antifail

-- | Rename a pattern
renamePatt :: Patt Raw -> R (Patt Renamed)
renamePatt x00 =
  withLoc x00 $
    evalStateT (loop x00) M.empty where
  loop :: Patt Raw ->
          StateT (M.Map (Either (Lid Raw) (TyVar Raw)) Loc)
            Renaming (Patt Renamed)
  loop x0 = case x0 of
    [pa| _ |] ->
      return [pa|+ _ |]
    [pa| $lid:l |] -> do
      l' <- var _loc l
      return [pa|+ $lid:l' |]
    [pa| $quid:qu $opt:mx |] -> do
      qu' <- lift $ getDatacon qu
      mx' <- traverse loop mx
      return [pa|+ $quid:qu' $opt:mx' |]
    [pa| `$uid:qu $opt:mx |] -> do
      let qu' = trivialRename qu
      mx' <- traverse loop mx
      return [pa|+ `$uid:qu' $opt:mx' |]
    [pa| ($x1, $x2) |] -> do
      x1' <- loop x1
      x2' <- loop x2
      return [pa|+ ($x1', $x2') |]
    [pa| $lit:lit |] -> do
      lit' <- lift $ renameLit lit
      return [pa|+ $lit:lit' |]
    [pa| $x as $lid:l |] -> do
      x' <- loop x
      l' <- var _loc l
      return [pa|+ $x' as $lid:l' |]
    [pa| ! $x |] -> do
      x' <- loop x
      return [pa| ! $x' |]
    [pa| $x : $t |] -> do
      x' <- loop x
      t' <- lift $ renameType t
      return [pa| $x' : $t' |]
    [pa| $anti:a |] -> do
      $antifail
  --
  var loc1 l = do
    seen <- get
    case M.lookup (Left l) seen of
      Just loc2 -> lift (repeated "Variable" l "pattern" [loc1, loc2])
      Nothing   -> do
        put (M.insert (Left l) loc1 seen)
        lift (withLoc loc1 (bindVar l))

-- | Univerally-quantify all free type variables
closeType :: Type Raw -> Type Raw
closeType t = foldr tyAll t (annotFtvSet t)

addVal     :: Lid Raw -> R (Lid Renamed)
addType    :: Lid Raw -> Renamed -> R (Lid Renamed)
addMod     :: Uid Raw -> R a -> R (Uid Renamed, a)

addVal = bindVar

addType l i = do
  let l' = renLid i l
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
  | SigAt      { renInfoLoc :: Loc, renInfoQUid :: QUid Renamed }
  | VariableAt { renInfoLoc :: Loc, renInfoQLid :: QLid Renamed }
  | TyconAt    { renInfoLoc :: Loc, renInfoQLid :: QLid Renamed }
  | DataconAt  { renInfoLoc :: Loc, renInfoQUid :: QUid Renamed }
  deriving Show

-- | For the REPL to find out where identifiers are bound and their
--   renamed name for looking up type info
getRenamingInfo :: Ident Raw -> RenameState -> [RenamingInfo]
getRenamingInfo ident RenameState { savedEnv = e } =
  catMaybes $ case view ident of
    Left ql  -> [ look tycons ql TyconAt,
                  look vars ql VariableAt ]
    Right qu -> [ look sigs qu SigAt,
                  look modules qu ModuleAt,
                  look datacons qu DataconAt ]
  where
    look prj qx build = case envLookup prj qx e of
      Left _                    -> Nothing
      Right (J ps (x', loc, _)) -> Just (build loc (J ps x'))

-- Open the given module, if it exists.
renamingEnterScope    :: Uid i -> RenameState -> RenameState
renamingEnterScope u r =
  let e  = savedEnv r in
  case M.lookup (uid (unUid u)) (modules e) of
    Nothing -> r
    Just (_, _, (_, e'))
            -> r { savedEnv = e `mappend` e' }

-- | Test runner for renaming an expression
_re :: Expr Raw -> IO (Expr Renamed)
_re e = fst <$> runRenamingM True bogus renameState0 (renameExpr e)

-- | Test runner for renaming an declaration
_rd :: Decl Raw -> IO (Decl Renamed)
_rd d = fst <$> runRenamingM True bogus renameState0 (renameDecl d)

_loc = initial "<interactive>"


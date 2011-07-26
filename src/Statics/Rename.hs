module Statics.Rename (
  -- * The renaming monad and runners
  Renaming, runRenaming, runRenamingM,
  renameMapM,
  -- * State between renaming steps
  RenameState, renameState0,
  -- ** Adding the basis
  addVal, addType, addMod,
  -- * Renamers
  renameProg, renameDecls, renameDecl, renameType, renameSigItem,
  -- * REPL query
  getRenamingInfo, RenamingInfo(..),
  renamingEnterScope,
) where

import Error

import Meta.Quasi
import AST hiding ((&))
import Data.Loc
import AST.TypeAnnotation
import qualified AST.Notable
import Util
import Syntax.Ppr (Ppr(..))

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
    datacons = M.singleton (ident "()") (ident "()", mkBogus "built-in", ())
  },
  savedCounter  = renamed0
}

-- | Generate a renamer error.
renameErrorStop :: Message V -> R a
renameErrorStop msg0 = do
  throwAlms (AlmsError RenamerPhase bogus msg0)

-- | Generate a renamer error, but keep going.
renameError :: Bogus a => Message V -> R a
renameError msg0 = do
  reportAlms (AlmsError RenamerPhase bogus msg0)
  return bogus

renameBug :: String -> String -> R a
renameBug culprit msg0 = do
  throwAlms (almsBug RenamerPhase culprit msg0)

-- | The renaming monad: Reads a context, writes a module, and
--   keeps track of a renaming counter state.
newtype Renaming a = R {
  unR :: RWST Context Module RState (AlmsErrorT Identity) a
} deriving (Functor, MonadAlmsError)

-- | The threaded state of the renamer.
newtype RState = RState {
  -- | The gensym counter:
  rsCounter :: Renamed
}

instance Monad Renaming where
  return  = R . return
  m >>= k = R (unR m >>= unR . k)
  fail    = renameErrorStop . [msg| $words:1 |]

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

instance MonadError [AlmsError] Renaming where
  throwError = throwAlmsList
  catchError = catchAlms

-- | The renaming environment
data Env = Env {
  tycons          :: !(EnvMap TypId  [ConId Raw]),
  vars            :: !(EnvMap VarId  ()),
  datacons        :: !(EnvMap ConId  ()),
  modules         :: !(EnvMap ModId  (Module, Env)),
  sigs            :: !(EnvMap SigId  (Module, Env)),
  tyvars          :: !(EnvMap Lid    (QLit, Bool))
} deriving Show

type EnvMap f i = M.Map (f Raw) (f Renamed, Loc, i)

-- | A module item is one of 5 renaming entries, an empty module, r
--   a pair of modules.  Note that while type variables are not actual
--   module items, they are exported from patterns, so it's useful to
--   have them here.
type Module = [ModItem]

data ModItem
  = MdTycon   !Loc !(TypId Raw) !(TypId Renamed) ![ConId Raw]
  | MdVar     !Loc !(VarId Raw) !(VarId Renamed)
  | MdDatacon !Loc !(ConId Raw) !(ConId Renamed)
  | MdModule  !Loc !(ModId Raw) !(ModId Renamed) !Module
  | MdSig     !Loc !(SigId Raw) !(SigId Renamed) !Module
  | MdTyvar   !Loc !(TyVar Raw) !(TyVar Renamed)
  deriving Show

-- | The renaming context, which includes the environment (which is
--   persistant), and other information with is not
data Context = Context {
  env      :: !Env,
  allocate :: !Bool,
  inExpr   :: !Bool
}

-- | Run a renaming computation
runRenaming :: Bool -> Loc -> RenameState -> Renaming a ->
               Either [AlmsError] (a, RenameState)
runRenaming nonTrivial loc saved action = do
  runIdentity $
    runAlmsErrorT $ withLocation loc $ do
      (result, rstate, md) <-
        runRWST (unR action)
          Context {
            env      = savedEnv saved,
            allocate = nonTrivial,
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
runRenamingM = either throwAlmsList return <$$$$> runRenaming

-- | Alias
type R a  = Renaming a

instance Monoid Env where
  mempty = Env M.empty M.empty M.empty M.empty M.empty M.empty
  mappend (Env a1 a2 a3 a4 a5 a6) (Env b1 b2 b3 b4 b5 b6) =
    Env (a1 & b1) (a2 & b2) (a3 & b3) (a4 & b4) (a5 & b5) (a6 & b6)
      where a & b = M.union b a

instance Bogus Env where bogus = mempty

-- | Open a module into an environment
envify :: Module -> Env
envify  = foldMap envifyItem

envifyItem :: ModItem -> Env
envifyItem (MdTycon loc l l' dcs)
  = mempty { tycons   = M.singleton l (l', loc, dcs) }
envifyItem (MdVar loc l l')
  = mempty { vars = M.singleton l (l', loc, ()) }
envifyItem (MdDatacon loc u u')
  = mempty { datacons = M.singleton u (u', loc, ()) }
envifyItem (MdModule loc u u' md)
  = mempty { modules = M.singleton u (u',loc,(md,envify md)) }
envifyItem (MdSig loc u u' md)
  = mempty { sigs = M.singleton u (u',loc,(md,envify md)) }
envifyItem (MdTyvar loc tv tv')
  = mempty { tyvars = M.singleton (tvname tv)
                                  (tvname tv',loc,(tvqual tv', True)) }

-- | Like 'asks', but in the 'R' monad
withContext :: (Context -> R a) -> R a
withContext  = R . (ask >>=) . fmap unR

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
  skip <- R (asks inExpr)
  ((), md) <- steal $
    if skip
      then return ()
      else traverse_ bindTyvar (annotFtvSet stx)
  inModule md (R (local (\e -> e { inExpr = True }) (unR action)))

-- | Hide any annotation type variables that were in scope.
hideAnnotationTVs :: R a -> R a
hideAnnotationTVs = 
  R . local (\e -> e { inExpr = False }) . unR .
    local (\e -> e { tyvars = each <$> tyvars e })
  where each (a, b, (c, _)) = (a, b, (c, False))

-- | Temporarily stop allocating unique ids
don'tAllocate :: R a -> R a
don'tAllocate = R . local (\cxt -> cxt { allocate = False }) . unR

-- | Generate an unbound name error
unbound :: (Ppr a, Bogus b) => String -> a -> R b
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
repeated :: (Ppr a, Bogus b) => String -> a -> String -> [Loc] -> R b
repeated what a inwhat locs =
  renameError $ repeatedMsg what [msg| $q:a |] inwhat locs

-- | Generate an error about a name declared twice
repeatedTVs :: Bogus b => [TyVar i] -> String -> R b
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
getAllVariables :: Module -> [QVarId Renamed]
getAllVariables = S.toList . foldMap loop where
  loop (MdVar _ _ l')       = S.singleton (J [] l')
  loop (MdModule _ _ u' md) = S.mapMonotonic (\(J us l) -> J (u':us) l)
                                             (foldMap loop md)
  loop _                    = S.empty

-- | Look up something in an environment
envLookup :: (Ord k, Show k) =>
             (Env -> M.Map k k') ->
             Path (ModId Raw) k ->
             Env ->
             Either (Maybe (Path (ModId Renamed) (ModId Raw)))
                    (Path (ModId Renamed) k')
envLookup prj = loop [] where
  loop ms' (J []     x) e = case M.lookup x (prj e) of
    Just x' -> Right (J (reverse ms') x')
    Nothing -> Left Nothing
  loop ms' (J (m:ms) x) e = case M.lookup m (modules e) of
    Just (m', _, (_, e')) -> loop (m':ms') (J ms x) e'
    Nothing               -> Left (Just (J (reverse ms') m))

-- | Look up something in the environment
getGenericFull :: (Ord k, Show k, Bogus k') =>
              String -> (Env -> M.Map k k') ->
              Path (ModId Raw) k -> R (Path (ModId Renamed) k')
getGenericFull what prj qx = do
  e <- ask
  case envLookup prj qx e of
    Right qx'     -> return qx'
    Left Nothing  -> unbound what qx
    Left (Just m) -> unbound "Module" m

-- | Look up something in the environment
getGeneric :: (Ord (f Raw), Show (f Raw), Bogus i, Bogus (f Renamed)) =>
              String -> (Env -> EnvMap f i) ->
              Path (ModId Raw) (f Raw) -> R (Path (ModId Renamed) (f Renamed))
getGeneric = liftM (fmap (\(qx', _, _) -> qx')) <$$$> getGenericFull

-- | Look up a variable in the environment
getVar :: QVarId Raw -> R (QVarId Renamed)
getVar  = getGeneric "Variable" vars

-- | Look up a data constructor in the environment
getDatacon :: QConId Raw -> R (QConId Renamed)
getDatacon  = getGeneric "Data constructor" datacons

-- | Look up a type in the environment
getTycon :: QTypId Raw -> R (QTypId Renamed)
getTycon  = getGeneric "Type constructor" tycons

-- | Look up a type with constructors in the environment
getTyconFull :: QTypId Raw -> R (QTypId Renamed, [ConId Raw])
getTyconFull qtid = do
  J ps (tid, _, cids) <- getGenericFull "Type name" tycons qtid
  return (J ps tid, cids)

-- | Look up a module in the environment
getModule :: QModId Raw -> R (QModId Renamed, Module, Env)
getModule  = liftM pull . getGenericFull "Structure" modules
  where
    pull (J ps (qu, _, (m, e))) = (J ps qu, m, e)

-- | Look up a module in the environment
getSig :: QSigId Raw -> R (QSigId Renamed, Module, Env)
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
               (Loc -> ident -> ident' -> ModItem) ->
               ident -> R ident'
bindGeneric ren build x = do
  case prjAnti x of
    Just a  -> $antifail
    Nothing -> return ()
  new <- newRenamed
  loc <- getLocation
  let x' = ren new x
  tell [build loc x x']
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
bindVar :: VarId Raw -> R (VarId Renamed)
bindVar  = bindGeneric renId MdVar

-- | Get a new name for a variable binding
bindTycon :: TypId Raw -> [ConId Raw] -> R (TypId Renamed)
bindTycon l0 dcs = bindGeneric renId build l0
  where build loc old new = MdTycon loc old new dcs

-- | Get a new name for a data constructor binding
bindDatacon :: ConId Raw -> R (ConId Renamed)
bindDatacon = bindGeneric renId MdDatacon

-- | Get a new name for a module, and bind it in the environment
bindModule :: ModId Raw -> Module -> R (ModId Renamed)
bindModule u0 md = bindGeneric renId build u0
  where build loc old new = MdModule loc old new md

-- | Get a new name for a signature, and bind it in the environment
bindSig :: SigId Raw -> Module -> R (SigId Renamed)
bindSig u0 md = bindGeneric renId build u0
  where build loc old new = MdSig loc old new md

-- | Add a type variable to the scope
bindTyvar :: TyVar Raw -> R (TyVar Renamed)
bindTyvar tv = do
  e <- asks tyvars
  case M.lookup (tvname tv) e of
    Nothing                      -> bindGeneric renId MdTyvar tv
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
renameDecl d0 = withLocation d0 $ case d0 of
  [dc| let $x = $e |] -> do
    x'  <- renamePatt x
    e'  <- renameExpr e
    return [dc|+ let $x' = $e' |]
  [dc| let rec $list:bns |] -> do
    (bns', md) <- renameBindings bns
    tell md
    return [dc|+ let rec $list:bns' |]
  [dc| type $tid:lhs = type $qtid:rhs |] -> do
    (rhs', dcs) <- getTyconFull rhs
    lhs'        <- bindTycon lhs dcs
    mapM_ bindDatacon dcs
    return [dc|+ type $tid:lhs' = type $qtid:rhs' |]
  [dc| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [dc|+ type $list:tds' |]
  [dc| abstype $list:ats with $list:ds end |] -> do
    let bindEach [atQ| $anti:a |] = $antifail
        bindEach (N _ (AbsTy _ _ [tdQ| $anti:a |])) = $antifail
        bindEach (N note at) = withLocation note $ do
          let l = tdName (dataOf (atdecl at))
          bindTycon l []
          return (l, getLoc note)
    (llocs, mdT) <- listen $ mapM bindEach ats
    case unique fst llocs of
      Nothing -> return ()
      Just (l, locs) ->
        repeated "Type declaration for" l "abstype group" (snd <$> locs)
    (ats', mdD) <-
      steal $
        inModule mdT $
          forM ats $ \at -> withLocation at $ case dataOf at of
            AbsTy variances qe td -> do
              (Just qe', td') <- renameTyDec (Just qe) td
              return (absTy variances qe' td' <<@ at)
            AbsTyAnti a -> $antifail
    -- Don't tell mdD upward, since we're censoring the datacons
    ds' <- inModule (mdT `mappend` mdD) $ renameDecls ds
    return [dc|+ abstype $list:ats' with $list:ds' end |]
  [dc| module INTERNALS = $me1 |] ->
    R $ local (\context -> context { allocate = False }) $ unR $ do
      let u = ident "INTERNALS"
      (me1', md) <- steal $ renameModExp me1
      u' <- bindModule u md
      return [dc|+ module $mid:u' = $me1' |]
  [dc| module $mid:u = $me1 |] -> do
    (me1', md) <- steal $ renameModExp me1
    u' <- bindModule u md
    return [dc|+ module $mid:u' = $me1' |]
  [dc| module type $sid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [dc|+ module type $sid:u' = $se1' |]
  [dc| open $me1 |] -> do
    me1' <- renameModExp me1
    return [dc|+ open $me1' |]
  [dc| local $list:ds1 with $list:ds2 end |] -> do
    (ds1', md) <- steal $ renameDecls ds1
    ds2' <- inModule md $ renameDecls ds2
    return [dc| local $list:ds1' with $list:ds2' end |]
  [dc| exception $cid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- traverse renameType mt
    return [dc|+ exception $cid:u' of $opt:mt' |]
  [dc| $anti:a |] -> $antifail

renameTyDecs :: [TyDec Raw] -> R [TyDec Renamed]
renameTyDecs tds = withLocation tds $ do
  let bindEach [tdQ| $anti:a |] = $antifail
      bindEach (N note td)       = withLocation note $ do
        bindTycon (tdName td) (tdMaybeCons td)
        return (tdName td, getLoc note)
  (llocs, md) <- listen $ mapM bindEach tds
  case unique fst llocs of
    Nothing -> return ()
    Just (l, locs) ->
      repeated "Type declaration for" l "type group" (snd <$> locs)
  inModule md $ mapM (liftM snd . renameTyDec Nothing) tds

tdMaybeCons :: TyDec' Raw -> [ConId Raw]
tdMaybeCons TdDat { tdAlts = alts } = fst <$> alts
tdMaybeCons _                       = []

renameTyDec :: Maybe (QExp Raw) -> TyDec Raw ->
               R (Maybe (QExp Renamed), TyDec Renamed)
renameTyDec _   (N _ (TdAnti a)) = $antierror
renameTyDec mqe (N note (TdSyn l clauses)) = withLocation note $ do
  case mqe of
    Nothing -> return ()
    Just _  ->
      renameBug "renameTyDec" "can’t rename QExp in context of type synonym"
  J [] l' <- getTycon (J [] l)
  clauses' <- forM clauses $ \(ps, rhs) -> withLocation ps $ do
    (ps', md) <- steal $ renameTyPats ps
    rhs' <- inModule md $ renameType rhs
    return (ps', rhs')
  return (Nothing, tdSyn l' clauses' <<@ note)
renameTyDec mqe (N note td)      = withLocation note $ do
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
        cons' <- forM cons $ \(u, mt) -> withLocation mt $ do
          -- XXX Why trivial?
          let u' = renId trivialId u
          tell [MdDatacon (getLoc mt) u u']
          mt'   <- traverse renameType mt
          return (u', mt')
        return (tdDat l' tvs' cons')
      TdAnti a -> $antifail
    return (mqe', td' <<@ note)

renameModExp :: ModExp Raw -> R (ModExp Renamed)
renameModExp me0 = withLocation me0 $ case me0 of
  [meQ| struct $list:ds end |] -> do
    ds' <- renameDecls ds
    return [meQ|+ struct $list:ds' end |]
  [meQ| $qmid:qu $list:_ |] -> do
    (qu', md, _) <- getModule qu
    let qls = getAllVariables md
    tell md
    return [meQ|+ $qmid:qu' $list:qls |]
  [meQ| $me1 : $se2 |] -> do
    (me1', md1) <- steal $ renameModExp me1
    (se2', md2) <- steal $ renameSigExp se2
    onlyInModule md1 $ sealWith md2
    return [meQ| $me1' : $se2' |]
  [meQ| $anti:a |] -> $antifail

renameSigExp :: SigExp Raw -> R (SigExp Renamed)
renameSigExp se0 = withLocation se0 $ case se0 of
  [seQ| sig $list:sgs end |] -> do
    (sgs', md) <- listen $ don'tAllocate $ renameMapM renameSigItem sgs
    onlyInModule mempty $ checkSigDuplicates md
    return [seQ|+ sig $list:sgs' end |]
  [seQ| $qsid:qu $list:_ |] -> do
    (qu', md, _) <- getSig qu
    let qls = getAllVariables md
    tell md
    return [seQ|+ $qsid:qu' $list:qls |]
  [seQ| $se1 with type $list:tvs $qtid:ql = $t |] -> do
    (se1', md) <- listen $ renameSigExp se1
    ql' <- onlyInModule md $ getTycon ql
    case unique id tvs of
      Nothing      -> return ()
      Just (_, tvs') -> repeatedTVs tvs' "with-type"
    (tvs', mdtvs) <- steal $ mapM bindTyvar tvs
    t' <- inModule mdtvs $ renameType t
    return [seQ|+ $se1' with type $list:tvs' $qtid:ql' = $t' |]
  [seQ| $anti:a |] -> $antifail

checkSigDuplicates :: Module -> R ()
checkSigDuplicates md = case md of
    []                   -> return ()
    md1:md2              -> do
      checkItem md1
      inModule [md1] $ checkSigDuplicates md2

  where
    checkItem item = case item of
      MdTycon   loc l  _ _ -> mustFail loc "Type"        l $ getTycon (J [] l)
      MdVar     loc l  _   -> mustFail loc "Variable"    l $ getVar (J [] l)
      MdDatacon loc u  _   -> mustFail loc "Constructor" u $ getDatacon (J [] u)
      MdModule  loc u  _ _ -> mustFail loc "Structure"   u $ getModule (J [] u)
      MdSig     loc u  _ _ -> mustFail loc "Signature"   u $ getSig (J [] u)
      MdTyvar   loc tv _   -> mustFail loc "Tyvar"      tv $ getTyvar tv
    mustFail loc kind which check = do
      failed <- (False <$ check) `catchError` \_ -> return True
      unless failed $ do
        withLocation loc $
          repeated kind which "signature" []

sealWith :: Module -> R ()
sealWith = mapM_ (each Nothing) where
  each b moditem = case moditem of
    MdTycon   _ l _ _  -> do
      (l', loc, cs') <- locate b "type constructor" tycons l
      tell [MdTycon loc l l' cs']
    MdVar     _ l _   -> do
      (l', loc, _) <- locate b "variable" vars l
      tell [MdVar loc l l']
    MdDatacon _ u _   -> do
      (u', loc, _) <- locate b "data constructor" datacons u
      tell [MdDatacon loc u u']
    MdModule  _ u _ md2 -> do
      (u', loc, (md1, _)) <- locate b "module" modules u
      ((), md1') <- steal $ onlyInModule md1 $ mapM_ (each b) md2
      tell [MdModule loc u u' md1']
    MdSig     _ u _ md2 -> do
      (u', loc, (md1, _)) <- locate b "module type" sigs u
      ((), _   ) <- steal $ onlyInModule md2 $ mapM_ (each (Just (Left u))) md1
      ((), md1') <- steal $ onlyInModule md1 $ mapM_ (each (Just (Right u))) md2
      tell [MdSig loc u u' md1']
    MdTyvar   _ _ _   ->
      renameBug "sealWith" "signature can’t declare type variable"
  locate b what prj name = do
    m <- asks prj
    case M.lookup name m of
      Just name' -> return name'
      Nothing    -> renameError $
        case b of
          Nothing -> [msg|
            In signature matching, structure is missing
            $words:what $q:name,
            which is present in ascribed signature.
          |]
          Just (Left u) -> [msg|
            In exact signature matching (for nested signature $u)
            found unexpected $words:what $q:name.
          |]
          Just (Right u) -> [msg|
            In exact signature matching (for nested signature $u)
            missing expected $words:what $q:name.
          |]

-- | Rename a signature item and return the environment
--   that they bind
renameSigItem :: SigItem Raw -> R (SigItem Renamed)
renameSigItem sg0 = withLocation sg0 $ case sg0 of
  [sgQ| val $vid:l : $t |] -> do
    l' <- bindVar l
    t' <- renameType (closeType t)
    return [sgQ|+ val $vid:l' : $t' |]
  [sgQ| type $list:tds |] -> do
    tds' <- renameTyDecs tds
    return [sgQ|+ type $list:tds' |]
  [sgQ| type $tid:lhs = type $qtid:rhs |] -> do
    (rhs', dcs) <- getTyconFull rhs
    lhs'        <- bindTycon lhs dcs
    mapM_ bindDatacon dcs
    return [sgQ|+ type $tid:lhs' = type $qtid:rhs' |]
  [sgQ| module $mid:u : $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindModule u md
    return [sgQ|+ module $mid:u' : $se1' |]
  [sgQ| module type $sid:u = $se1 |] -> do
    (se1', md) <- steal $ renameSigExp se1
    u' <- bindSig u md
    return [sgQ|+ module type $sid:u' = $se1' |]
  [sgQ| include $se1 |] -> do
    se1' <- renameSigExp se1
    return [sgQ|+ include $se1' |]
  [sgQ| exception $cid:u of $opt:mt |] -> do
    u'  <- bindDatacon u
    mt' <- traverse renameType mt
    return [sgQ|+ exception $cid:u' of $opt:mt' |]
  [sgQ| $anti:a |] -> $antifail

-- | Rename an expression
renameExpr :: Expr Raw -> R (Expr Renamed)
renameExpr e00 = withAnnotationTVs e00 $ loop e00 where
  loop e0 = withLocation e0 $ case e0 of
    [ex| $qvid:ql |] -> do
      ql' <- getVar ql
      return [ex|+ $qvid:ql' |]
    [ex| $lit:lit |] -> do
      lit' <- renameLit lit
      return [ex|+ $lit:lit' |]
    [ex| $qcid:qu $opt:me |] -> do
      qu' <- getDatacon qu
      me' <- traverse loop me
      return [ex|+ $qcid:qu' $opt:me' |]
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
    [ex| { $list:flds | $e2 } |] -> do
      flds' <- mapM renameField flds
      e2'   <- loop e2
      return [ex|+ { $list:flds' | $e2' } |]
    [ex| {+ $list:flds | $e2 +} |] -> do
      flds' <- mapM renameField flds
      e2'   <- loop e2
      return [ex|+ {+ $list:flds' | $e2' +} |]
    [ex| $e1.$uid:u |] -> do
      let u' = trivialRename u
      e1' <- loop e1
      return [ex|+ $e1'.$uid:u' |]
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
renameCaseAlt ca0 = withLocation ca0 $ case ca0 of
  [caQ| $x -> $e |] -> do
    (x', md) <- steal $ renamePatt x
    e' <- inModule md $ renameExpr e
    return [caQ|+ $x' -> $e' |]
  [caQ| #$uid:lab -> $e |] -> do
    let lab' = trivialRename lab
    e' <- renameExpr e
    return [caQ|+ #$uid:lab' -> $e' |]
  [caQ| #$uid:lab $x -> $e |] -> do
    let lab' = trivialRename lab
    (x', md) <- steal $ renamePatt x
    e' <- inModule md $ renameExpr e
    return [caQ|+ #$uid:lab' $x' -> $e' |]
  [caQ| $antiC:a |] -> $antifail

-- | Rename a set of let rec bindings
renameBindings :: [Binding Raw] -> R ([Binding Renamed], Module)
renameBindings bns = withAnnotationTVs bns $ withLocation bns $ do
  lxes <- forM bns $ \bn ->
    case bn of
      [bnQ| $vid:x = $e |] -> return (_loc, x, e)
      [bnQ| $antiB:a |]    -> $antifail
  case unique (\(_,x,_) -> x) lxes of
    Nothing          -> return ()
    Just (x, locs) ->
      repeated "Variable binding for" x "let-rec" (sel1 <$> locs)
  let bindEach rest (l,x,e) = withLocation l $ do
        x' <- bindVar x
        return ((l,x',e):rest)
  (lxes', md) <- steal $ foldM bindEach [] lxes
  bns' <- inModule md $
            forM (reverse lxes') $ \(l,x',e) -> withLocation l $ do
              let _loc = l
              e'  <- renameExpr e
              return [bnQ|+ $vid:x' = $e' |]
  return (bns', md)

-- | Rename a record field
renameField :: Field Raw → R (Field Renamed)
renameField [fdQ| $uid:u = $e |] = do
  let u' = trivialRename u
  e' ← renameExpr e
  return [fdQ|+ $uid:u' = $e' |]
renameField [fdQ| $antiF:a |] = $antifail

-- | Rename a type
renameType :: Type Raw -> R (Type Renamed)
renameType t0 = withLocation t0 $ case t0 of
  [ty| ($list:ts) $qtid:ql |] -> do
    ql' <- getTycon ql
    ts' <- mapM renameType ts
    return [ty|+ ($list:ts') $qtid:ql' |]
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
renameTyPats x00 = evalStateT (mapM loop x00) M.empty where
  loop :: TyPat Raw ->
          StateT (M.Map (Lid Raw) (TyVar Raw, Loc)) Renaming (TyPat Renamed)
  loop x0 = withLocation x0 $ case x0 of
    [tpQ| $antiP:a |] -> $antifail
    N note (TpVar tv var) -> do
      tv' <- tyvar (getLoc note) tv
      return (tpVar tv' var <<@ note)
    N note (TpRow tv var) -> do
      tv' <- tyvar (getLoc note) tv
      return (tpRow tv' var <<@ note)
    [tpQ| ($list:tps) $qtid:ql |] -> do
      ql'  <- lift (withLocation _loc (getTycon ql))
      tps' <- mapM loop tps
      return [tpQ|+ ($list:tps') $qtid:ql' |]
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
renameQExp qe0 = withLocation qe0 $ case qe0 of
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
renamePatt x00 = evalStateT (loop x00) M.empty where
  loop :: Patt Raw ->
          StateT (M.Map (VarId Raw) Loc)
            Renaming (Patt Renamed)
  loop x0 = withLocation x0 $ case x0 of
    [pa| _ |] ->
      return [pa|+ _ |]
    [pa| $vid:l |] -> do
      l' <- var _loc l
      return [pa|+ $vid:l' |]
    [pa| $qcid:qu $opt:mx |] -> do
      qu' <- lift $ getDatacon qu
      mx' <- traverse loop mx
      return [pa|+ $qcid:qu' $opt:mx' |]
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
    [pa| $x as $vid:l |] -> do
      x' <- loop x
      l' <- var _loc l
      return [pa|+ $x' as $vid:l' |]
    [pa| { $uid:u = $x | $y } |] -> do
      let u' = trivialRename u
      x' <- loop x
      y' <- loop y
      return [pa|! { $uid:u' = $x' | $y' } |]
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
  var loc1 vid = do
    seen <- get
    case M.lookup vid seen of
      Just loc2 -> lift (repeated "Variable" vid "pattern" [loc1, loc2])
      Nothing   -> do
        put (M.insert vid loc1 seen)
        lift (withLocation loc1 (bindVar vid))

-- | Univerally-quantify all free type variables
closeType :: Type Raw -> Type Raw
closeType t = foldr tyAll t (annotFtvSet t)

addVal     :: VarId Raw -> R (VarId Renamed)
addType    :: TypId Raw -> Renamed -> [ConId Raw] -> R (TypId Renamed)
addMod     :: ModId Raw -> R a -> R (ModId Renamed, a)

addVal = bindVar

addType l i dcs = do
  let l' = renId i l
  loc <- getLocation
  tell [MdTycon loc l l' dcs]
  return l'

addMod u body = do
  let u' = renId trivialId u
  (a, md) <- steal body
  loc <- getLocation
  tell [MdModule loc u u' md]
  return (u', a)

-- | Result for 'getRenamingInfo'
data RenamingInfo
  = ModuleAt   { renInfoLoc :: Loc, renInfoQModId :: QModId Renamed }
  | SigAt      { renInfoLoc :: Loc, renInfoQSigId :: QSigId Renamed }
  | VariableAt { renInfoLoc :: Loc, renInfoQVarId :: QVarId Renamed }
  | TyconAt    { renInfoLoc :: Loc, renInfoQTypId :: QTypId Renamed }
  | DataconAt  { renInfoLoc :: Loc, renInfoQConId :: QConId Renamed }
  deriving Show

-- | For the REPL to find out where identifiers are bound and their
--   renamed name for looking up type info
getRenamingInfo :: Ident Raw -> RenameState -> [RenamingInfo]
getRenamingInfo name RenameState { savedEnv = e } =
  catMaybes $ case view name of
    Left ql  -> [ look tycons   (TypId <$> ql) TyconAt,
                  look vars     (VarId <$> ql) VariableAt ]
    Right qu -> [ look sigs     (SigId <$> qu) SigAt,
                  look modules  (ModId <$> qu) ModuleAt,
                  look datacons (ConId <$> qu) DataconAt ]
  where
    look prj qx build = case envLookup prj qx e of
      Left _                    -> Nothing
      Right (J ps (x', loc, _)) -> Just (build loc (J ps x'))

-- Open the given module, if it exists.
renamingEnterScope    :: ModId i -> RenameState -> RenameState
renamingEnterScope u r =
  let e  = savedEnv r in
  case M.lookup (renId trivialId u) (modules e) of
    Nothing -> r
    Just (_, _, (_, e'))
            -> r { savedEnv = e `mappend` e' }

-- | Test runner for renaming an expression
re :: Expr Raw -> Either [AlmsError] (Expr Renamed)
re e = fst <$> runRenaming True bogus renameState0 (renameExpr e)

-- | Test runner for renaming an declaration
rd :: Decl Raw -> Either [AlmsError] (Decl Renamed)
rd d = fst <$> runRenaming True bogus renameState0 (renameDecl d)

_loc :: Loc
_loc = initial "<interactive>"

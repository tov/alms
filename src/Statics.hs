-- | The external interface to the type checker
module Statics (
  -- * Type checking state
  StaticsState, staticsState0, staticsState0',
  -- ** Initial state
  addSignature, addPrimType,

  -- * Type checking operations
  typeCheckDecls, typeCheckProg,

  -- * Renaming and typing info
  -- ** Renaming
  Statics.getRenamingInfo, RenamingInfo(..),
  -- ** Constraint solving
  getConstraint,
  -- ** Type checking
  getVarInfo, getTypeInfo, getConInfo,
  -- ** Printing nice type names
  addTyNameContext, makeTyNames, makeT2SContext, staticsEnterScope,
) where

import Util
import Util.MonadRef
import AST.Ident (Raw, Renamed, Id(..))
import qualified AST
import Syntax.PprClass (Doc, setTyNames)
import Type
import Statics.Env
import Statics.Error
import Statics.Constraint
import Statics.Rename
import Statics.Decl

import Prelude ()
import qualified Data.List as List

---
--- TYPE CHECKING STATE
---

-- | The state of the renamer and type checker, parameterized by
--   a reference type.
data StaticsState r
  = StaticsState {
      ssRen     ∷ !RenameState,
      ssCon     ∷ !(ConstraintState (TV r) r),
      ssEnv     ∷ !(Γ (TV r))
    }

-- | The initial state of the type checker, parameterized by the
--   initial renaming state.
staticsState0 ∷ RenameState → StaticsState r
staticsState0 rs
  = StaticsState {
      ssRen     = rs,
      ssCon     = constraintState0,
      ssEnv     = mempty
    }

-- | The initial state of the type checker with no initial renaming
--   state.
staticsState0' ∷ StaticsState r
staticsState0' = staticsState0 renameState0

---
--- TYPE CHECKING OPERATIONS
---

-- | Type check a sequence of declarations.
typeCheckDecls ∷ (MonadAlmsError m, MonadRef r m) ⇒
                 StaticsState r →
                 [AST.Decl Raw] →
                 m ([AST.Decl Renamed],
                    [AST.SigItem R],
                    StaticsState r)
typeCheckDecls ss ds = do
  (ds', rs)             ← bailoutIfError $
    runRenamingM True bogus (ssRen ss) (renameDecls ds)
  ((ds'', γ', sig), cs) ← bailoutIfError . runConstraintT (ssCon ss) $ do
    tcDecls [] (ssEnv ss) ds' <* ensureSatisfiability
  let ss' = ss {
              ssRen     = rs,
              ssCon     = cs,
              ssEnv     = γ'
            }
  return (ds'', sigItemToStx (makeTyNames ss') <$> sig, ss')

-- | Type check a program.
typeCheckProg ∷ (MonadAlmsError m, MonadRef r m) ⇒
                StaticsState r →
                AST.Prog Raw →
                m (AST.Prog Renamed, Maybe (AST.Type Renamed))
typeCheckProg ss p = do
  (p', _)         ← bailoutIfError $
    runRenamingM True bogus (ssRen ss) (renameProg p)
  ((p'', mσ), _)  ← bailoutIfError . runConstraintT (ssCon ss) $ do
    tcProg (ssEnv ss) p' <* ensureSatisfiability
  return (p'', typeToStx' <$> mσ)

---
--- ADDING INITIAL BINDINGS
---

-- | Bind the contents of a signature in the environment.  This is used
--   for setting up some primitive types and values.
addSignature ∷ (MonadAlmsError m, MonadRef r m) ⇒
               StaticsState r →
               AST.SigExp Renamed →
               m (StaticsState r)
addSignature ss sigexp = do
  (sig, cs') ← runConstraintT (ssCon ss) (tcSigExp (ssEnv ss) sigexp)
  return ss {
    ssCon       = cs',
    ssEnv       = ssEnv ss =+= sigToEnv sig
  }

-- | Bind a primitive type constructor at top level.
addPrimType ∷ StaticsState r → TypId → TyCon → StaticsState r
addPrimType ss tid tc = ss { ssEnv = ssEnv ss =+= tid =:= tc }

---
--- INTERFACE FOR GETTING TYPE INFO
---

-- | Find out the renamed name of an identifier and where it was defined.
getRenamingInfo ∷ AST.Ident Raw → StaticsState r → [RenamingInfo]
getRenamingInfo = Statics.Rename.getRenamingInfo <$.> ssRen

-- | Find out the type of a variable
getVarInfo :: QVarId -> StaticsState r -> Maybe (AST.Type R)
getVarInfo vid ss = typeToStx (makeT2SContext ss) <$> ssEnv ss =..= vid

-- | Find out about a type
getTypeInfo :: QTypId -> StaticsState r -> Maybe TyCon
getTypeInfo tid ss = ssEnv ss =..= tid

-- Find out about a data constructor.  If it's an exception constructor,
-- return 'Right' with its parameter, otherwise return the type construtor
-- of the result type
getConInfo :: QConId -> StaticsState r ->
              Maybe (Either TyCon (Maybe (AST.Type R)))
getConInfo cid ss = typeToStx (makeT2SContext ss) <$$$> ssEnv ss =..= cid

-- | Get a printable representation of the current constraint-solving
--   state.
getConstraint ∷ StaticsState r → Doc
getConstraint = pprConstraintState . ssCon

-- Open the given module, if it exists.
staticsEnterScope       :: ModId -> StaticsState r -> StaticsState r
staticsEnterScope mid ss =
  case ssEnv ss =..= mid of
    Just (_, e') -> ss { ssEnv = ssEnv ss =+= e' }
    Nothing      -> ss

---
--- CHOOSING BEST TYPE NAMES
---

-- | Given the type checker state, add it to the context of a document
--   for printing type names in that document.
addTyNameContext :: StaticsState r → Doc → Doc
addTyNameContext  = setTyNames . makeTyNames

-- | Get the type name lookup gadget from the type checker state
makeTyNames :: StaticsState r → TyNames
makeTyNames ss
  = TyNames {
      tnLookup = getBestName ss,
      tnEnter  = \mid → makeTyNames (staticsEnterScope mid ss)
    }

-- | Make the type-syntactifying context from the type checker state
makeT2SContext :: StaticsState r →
                  T2SContext CurrentImpArrPrintingRule tv
makeT2SContext ss = t2sContext0 { t2sTyNames = makeTyNames ss }

-- | The status of a type name in an environment
data NameStatus
 -- | Bound to the expected type
 = Match
 -- | Not bound
 | NoMatch
 -- | Shadowed
 | Interfere
 deriving Eq

-- | In the given environment, what is the status of the given
--   type name?
getNameStatus :: StaticsState r → Int → QTypId → NameStatus
getNameStatus ss tag tid =
  case [ tid'
       | TyconAt _ tid' <- Statics.getRenamingInfo ql ss ] of
    tid':_ ->
      case getTypeInfo tid' ss of
        Just tc | tcId tc == tag  -> Match
                | otherwise       -> Interfere
        _                         -> NoMatch
    _     -> NoMatch
  where ql = J (map (AST.renId bogus) (jpath tid))
               (AST.ident (AST.idName (jname tid)))

-- | Names known to the pretty-printer that should always be used
--   exactly like this so that things print nicely.
intrinsicNames ∷ [(Int, String)]
intrinsicNames = first tcId <$>
  [ (tcVariant,  AST.tnVariant),
    (tcRecord,   AST.tnRecord),
    (tcRowEnd,   AST.tnRowEnd),
    (tcRowHole,  AST.tnRowHole),
    (tcRowMap,   AST.tnRowMap),
    (tcUn,       AST.tnUn),
    (tcAf,       AST.tnAf) ]

-- | Find the best name to refer to a type constructor.
--   The goal here is to get the shortest unambiguous name.
--    1. If the first parameter is True, we want an accurate name, so
--       skip to step 3.
--    2. If the unqualified name is bound to either the same type
--       or to nothing, then use the unqualified name.
--    3. Try qualifiying the name, starting with the last segment
--       and adding one at a time, and if any of these match, then
--       use that.
--    4. Otherwise, uglify the name, because it's probably gone
--       out of scope.
getBestName :: StaticsState r -> Int -> QTypId -> QTypId

getBestName ss tag qtid
  | Just str ← lookup tag intrinsicNames = qident str
  | otherwise                            =
    case tryQuals (jpath qtid) (jname qtid) of
      Just qtid'    → qtid'
      Nothing
        | AST.isTrivial (idTag (jname qtid))
        , NoMatch ← getNameStatus ss tag qtid
                    → qtid
        | otherwise → uglify
  where
    tryQuals mids tid = msum
      [ case getNameStatus ss tag (J mids' tid) of
          Match     -> Just (J mids' tid)
          _         -> Nothing
      | mids' <- reverse (List.tails mids) ]
    uglify
      | '?':_ ← show qtid = qtid
      | otherwise         = qtid { jpath = ident ('?':show tag) : jpath qtid }


-- | The external interface to the type checker
module Statics (
  -- * Type checking state
  StaticsState, staticsState0, staticsState0',
  -- ** Initial state
  addSignature, addPrimType,

  -- * Type checking operations
  typeCheckDecls, typeCheckProg,

  -- * Renaming and typing info
  Statics.getRenamingInfo, RenamingInfo(..),
  getVarInfo, getTypeInfo, getConInfo,
  staticsEnterScope,
) where

import Util
import Util.MonadRef
import AST.Ident (Raw, Renamed)
import qualified AST
import Type
import Statics.Env
import Statics.Error
import Statics.Constraint
import Statics.Rename
import Statics.Decl

import Prelude ()

---
--- TYPE CHECKING STATE
---

-- | The state of the renamer and type checker, parameterized by
--   a reference type.
data StaticsState r
  = StaticsState {
      ssRename       ∷ !RenameState,
      ssConstraint   ∷ !(ConstraintState (TV r) r),
      ssEnv          ∷ !(Γ (TV r))
    }

-- | The initial state of the type checker, parameterized by the
--   initial renaming state.
staticsState0 ∷ RenameState → StaticsState r
staticsState0 rs
  = StaticsState {
      ssRename          = rs,
      ssConstraint      = constraintState0,
      ssEnv             = mempty
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
  (ds', rs)         ← bailoutIfError $
    runRenamingM True bogus (ssRename ss) (renameDecls ds)
  ((ds'', sig), cs) ← bailoutIfError $
    runConstraintT (ssConstraint ss) (tcDecls [] (ssEnv ss) ds')
  let ss' = ss {
              ssRename     = rs,
              ssConstraint = cs,
              ssEnv        = ssEnv ss =+= sigToEnv sig
            }
  return (ds'', sigItemToStx' <$> sig, ss')

-- | Type check a program.
typeCheckProg ∷ (MonadAlmsError m, MonadRef r m) ⇒
                StaticsState r →
                AST.Prog Raw →
                m (AST.Prog Renamed, Maybe (AST.Type Renamed))
typeCheckProg ss p = do
  (p', _)         ← bailoutIfError $
    runRenamingM True bogus (ssRename ss) (renameProg p)
  ((p'', mσ), _)  ← bailoutIfError $
    runConstraintT (ssConstraint ss) (tcProg (ssEnv ss) p')
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
  (sig, cs') ← runConstraintT (ssConstraint ss) (tcSigExp (ssEnv ss) sigexp)
  return ss {
    ssConstraint = cs',
    ssEnv        = ssEnv ss =+= sigToEnv sig
  }

-- | Bind a primitive type constructor at top level.
addPrimType ∷ StaticsState r → TypId → TyCon → StaticsState r
addPrimType ss tid tc = ss { ssEnv = ssEnv ss =+= tid =:= tc }

---
--- INTERFACE FOR GETTING TYPE INFO
---

-- | Find out the renamed name of an identifier and where it was defined.
getRenamingInfo ∷ AST.Ident Raw → StaticsState r → [RenamingInfo]
getRenamingInfo = Statics.Rename.getRenamingInfo <$.> ssRename

-- | Find out the type of a variable
getVarInfo :: QVarId -> StaticsState r -> Maybe (AST.Type R)
getVarInfo vid ss = typeToStx' <$> ssEnv ss =..= vid

-- | Find out about a type
getTypeInfo :: QTypId -> StaticsState r -> Maybe TyCon
getTypeInfo tid ss = ssEnv ss =..= tid

-- Find out about a data constructor.  If it's an exception constructor,
-- return 'Right' with its parameter, otherwise return the type construtor
-- of the result type
getConInfo :: QConId -> StaticsState r ->
              Maybe (Either TyCon (Maybe (AST.Type R)))
getConInfo cid ss = typeToStx' <$$$> ssEnv ss =..= cid

-- Open the given module, if it exists.
staticsEnterScope       :: ModId -> StaticsState r -> StaticsState r
staticsEnterScope mid ss =
  case ssEnv ss =..= mid of
    Just (_, e') -> ss { ssEnv = ssEnv ss =+= e' }
    Nothing      -> ss

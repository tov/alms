{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      UnicodeSyntax
    #-}
-- | The external interface to the type checker
module Statics (
  -- * Type checking state
  StaticsState, staticsState0, staticsState0',
  -- ** Initial state
  addSignature, addPrimType,

  -- * Type checking operations
  typeCheckDecls, typeCheckProg,
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
                 m ([AST.Decl Renamed], Signature (TV r), StaticsState r)
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
  return (ds'', sig, ss')

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

{-
getVarInfo :: QLid R -> S -> Maybe Type
getVarInfo ql (S e _) = e =..= fmap Var ql

getTypeInfo :: QLid R -> S -> Maybe TyCon
getTypeInfo ql (S e _) = e =..= ql

-- Find out about a data constructor.  If it's an exception constructor,
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

-- Open the given module, if it exists.
staticsEnterScope    :: Uid R -> S -> S
staticsEnterScope u s =
  let e = sEnv s in
  case e =..= u of
    Just (_, e') -> s { sEnv = e =+= e' }
    Nothing      -> s

-- | Find out the parameter type of an exception
getExnParam :: Type -> Maybe (Maybe Type)
getExnParam (TyApp tc _ _)
  | tc == tcExn             = Just Nothing
getExnParam (TyFun _ t1 (TyApp tc _ _))
  | tc == tcExn             = Just (Just t1)
getExnParam _               = Nothing

-}

{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      StandaloneDeriving,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Decl (
  -- * Declarations
  Decl'(..), Decl, DeclNote(..), newDecl,
  -- ** Type declarations
  TyDec'(..), TyDec, AbsTy'(..), AbsTy,
  -- ** Modules
  ModExp'(..), ModExp, newModExp,
  -- ** Synthetic constructors
  -- | These fill in the source location fields with a bogus location
  dcLet, dcTyp, dcAbs, dcMod, dcOpn, dcLoc, dcExn, dcAnti,
  absTy, absTyAnti,
  tdAbs, tdSyn, tdDat, tdAnti,
  meStr, meName, meAnti,
  prog,

  -- * Programs
  Prog'(..), Prog,
  prog2decls
) where

import Meta.DeriveNotable
import Syntax.Notable
import Syntax.Anti
import Syntax.Kind
import Syntax.Ident
import Syntax.Type
import Syntax.Patt
import Syntax.Expr

import Data.Generics (Typeable(..), Data(..))
import qualified Data.Set as S
import qualified Data.Map as M

type Decl i   = N (DeclNote i) (Decl' i)
type ModExp i = N (DeclNote i) (ModExp' i)
type Prog i   = Located Prog' i
type AbsTy i  = Located AbsTy' i
type TyDec i  = Located TyDec' i

-- | A program is a sequence of declarations, maybe followed by an
-- expression
data Prog' i = Prog [Decl i] (Maybe (Expr i))
  deriving (Typeable, Data)

-- | Declarations
data Decl' i
  -- | Constant declaration
  = DcLet (Patt i) (Maybe (Type i)) (Expr i)
  -- | Type declaration
  | DcTyp [TyDec i]
  -- | Abstype block declaration
  | DcAbs [AbsTy i] [Decl i]
  -- | Module declaration
  | DcMod (Uid i) (ModExp i)
  -- | Module open
  | DcOpn (ModExp i)
  -- | Local block
  | DcLoc [Decl i] [Decl i]
  -- | Exception declaration
  | DcExn (Uid i) (Maybe (Type i))
  -- | Antiquote
  | DcAnti Anti
  deriving (Typeable, Data)

-- | A module expression
data ModExp' i
  -- | A module literal
  = MeStr [Decl i]
  -- | A module variable
  | MeName (QUid i) [QLid i]
  -- | An antiquote
  | MeAnti Anti
  deriving (Typeable, Data)

-- | Affine language type declarations
data TyDec' i
  -- | An abstract (empty) type
  = TdAbs {
      tdName      :: Lid i,
      tdParams    :: [TyVar i],
      -- | The variance of each parameter
      tdVariances :: [Variance],
      -- | Whether each parameter contributes to the qualifier
      tdQual      :: QExp i
    }
  -- | A type synonym
  | TdSyn {
      tdName      :: Lid i,
      tdParams    :: [TyVar i],
      tdRHS       :: Type i
    }
  -- | An algebraic datatype
  | TdDat {
      tdName      :: Lid i,
      tdParams    :: [TyVar i],
      tdAlts      :: [(Uid i, Maybe (Type i))]
    }
  | TdAnti Anti
  deriving (Typeable, Data)

-- | An abstract type needs to specify variances and the qualifier
data AbsTy' i
  = AbsTy {
      atvariance :: [Variance],
      atquals    :: QExp i,
      atdecl     :: TyDec i
    }
  | AbsTyAnti Anti
  deriving (Typeable, Data)

data DeclNote i
  = DeclNote {
      -- | source location
      dloc_  :: !Loc,
      -- | free variables
      dfv_   :: FvMap i,
      -- | defined variables
      ddv_   :: S.Set (QLid i)
    }
  deriving (Typeable, Data)

instance Locatable (DeclNote i) where
  getLoc = dloc_

instance Relocatable (DeclNote i) where
  setLoc note loc = note { dloc_ = loc }

instance Notable (DeclNote i) where
  newNote = DeclNote bogus M.empty S.empty

newDecl :: Id i => Decl' i -> Decl i
newDecl d0 = flip N d0 $ case d0 of
  DcLet p1 t2 e3 ->
    DeclNote {
      dloc_  = getLoc (p1, t2, e3),
      dfv_   = fv e3,
      ddv_   = qdv p1
    }
  DcTyp tds ->
    newNote {
      dloc_  = getLoc tds
    }
  DcAbs at1 ds2 ->
    newNote {
      dloc_  = getLoc (at1, ds2),
      dfv_   = fv ds2,
      ddv_   = S.unions (map qdv ds2)
    }
  DcMod u1 me2 ->
    DeclNote {
      dloc_  = getLoc me2,
      dfv_   = fv me2,
      ddv_   = S.mapMonotonic (\(J p n) -> J (u1:p) n) (qdv me2)
    }
  DcOpn me1 ->
    DeclNote {
      dloc_  = getLoc me1,
      dfv_   = fv me1,
      ddv_   = qdv me1
    }
  DcLoc ds1 ds2 ->
    DeclNote {
      dloc_  = getLoc (ds1, ds2),
      dfv_   = fv ds1 |+| (fv ds2 |--| qdv ds1),
      ddv_   = qdv ds2
    }
  DcExn _ t2 ->
    newNote {
      dloc_  = getLoc t2
    }
  DcAnti a ->
    newNote {
      dfv_  = antierror "fv" a,
      ddv_  = antierror "dv" a
    }

newModExp :: Id i => ModExp' i -> ModExp i
newModExp me0 = flip N me0 $ case me0 of
  MeStr ds ->
    DeclNote {
      dloc_  = getLoc ds,
      dfv_   = fv ds,
      ddv_   = qdv ds
    }
  MeName _ qls ->
    newNote {
      ddv_  = S.fromList qls
    }
  MeAnti a ->
    newNote {
      dfv_  = antierror "fv" a,
      ddv_  = antierror "dv" a
    }

instance Id i => Fv (N (DeclNote i) a) i where fv  = dfv_ . noteOf
instance Id i => Dv (N (DeclNote i) a) i where qdv = ddv_ . noteOf

deriveNotable 'newDecl   (''Id, [0]) ''Decl
deriveNotable 'newModExp (''Id, [0]) ''ModExp
deriveNotable ''AbsTy
deriveNotable ''TyDec
deriveNotable ''Prog

---
--- Syntax Utils
---

-- | Turn a program into a sequence of declarations by replacing
-- the final expression with a declaration of variable 'it'.
prog2decls :: Id i => Prog i -> [Decl i]
prog2decls (N _ (Prog ds (Just e)))
  = ds ++ [dcLet (paVar (lid "it")) Nothing e]
prog2decls (N _ (Prog ds Nothing))
  = ds

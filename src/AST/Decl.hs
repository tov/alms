{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      StandaloneDeriving,
      TemplateHaskell,
      TypeFamilies,
      TypeSynonymInstances #-}
module AST.Decl (
  -- * Declarations
  Decl'(..), Decl, DeclNote(..), newDecl,
  -- ** Type declarations
  TyDec'(..), TyDec, AbsTy'(..), AbsTy,
  -- ** Modules
  ModExp'(..), ModExp, newModExp,
  -- ** Signature
  SigExp'(..), SigExp, newSigExp,
  SigItem'(..), SigItem, newSigItem,
  -- ** Synthetic constructors
  -- | These fill in the source location fields with a bogus location
  dcLet, dcTyp, dcAbs, dcMod, dcSig, dcOpn, dcLoc, dcExn, dcAnti,
  absTy, absTyAnti,
  tdAbs, tdSyn, tdDat, tdAnti,
  meStr, meName, meAsc, meAnti,
  sgVal, sgTyp, sgMod, sgSig, sgInc, sgExn, sgAnti,
  seSig, seName, seWith, seAnti,
  prog,

  -- * Programs
  Prog'(..), Prog,
  prog2decls
) where

import Meta.DeriveNotable
import AST.Notable
import AST.Anti
import AST.Kind
import AST.Ident
import AST.Type
import AST.Patt
import AST.Expr

import Data.Generics (Typeable(..), Data(..))
import qualified Data.Set as S
import qualified Data.Map as M

type Decl i    = N (DeclNote i) (Decl' i)
type ModExp i  = N (DeclNote i) (ModExp' i)
type SigItem i = N (DeclNote i) (SigItem' i)
type SigExp i  = N (DeclNote i) (SigExp' i)
type Prog i    = Located Prog' i
type AbsTy i   = Located AbsTy' i
type TyDec i   = Located TyDec' i

-- | A program is a sequence of declarations, maybe followed by an
-- expression
data Prog' i = Prog [Decl i] (Maybe (Expr i))
  deriving (Typeable, Data)

-- | Declarations
data Decl' i
  -- | Constant declaration
  = DcLet (Patt i) (Expr i)
  -- | Type declaration
  | DcTyp [TyDec i]
  -- | Abstype block declaration
  | DcAbs [AbsTy i] [Decl i]
  -- | Module declaration
  | DcMod (ModId i) (ModExp i)
  -- | Signature declaration
  | DcSig (SigId i) (SigExp i)
  -- | Module open
  | DcOpn (ModExp i)
  -- | Local block
  | DcLoc [Decl i] [Decl i]
  -- | Exception declaration
  | DcExn (ConId i) (Maybe (Type i))
  -- | Antiquote
  | DcAnti Anti
  deriving (Typeable, Data)

-- | A module expression
data ModExp' i
  -- | A module literal
  = MeStr [Decl i]
  -- | A module variable
  | MeName (QModId i) [QVarId i]
  -- | A signature ascription
  | MeAsc (ModExp i) (SigExp i)
  -- | An antiquote
  | MeAnti Anti
  deriving (Typeable, Data)

-- | A signature item
data SigItem' i
  -- | A value
  = SgVal (VarId i) (Type i)
  -- | A type
  | SgTyp [TyDec i]
  -- | A module
  | SgMod (ModId i) (SigExp i)
  -- | A signature
  | SgSig (SigId i) (SigExp i)
  -- | Signature inclusion
  | SgInc (SigExp i)
  -- | An exception
  | SgExn (ConId i) (Maybe (Type i))
  -- | An antiquote
  | SgAnti Anti
  deriving (Typeable, Data)

-- | A module type expression
data SigExp' i
  -- | A signature literal
  = SeSig [SigItem i]
  -- | A signature variable
  | SeName (QSigId i) [QVarId i]
  -- | Type-level fibration
  | SeWith (SigExp i) (QTypId i) [TyVar i] (Type i)
  -- | An antiquote
  | SeAnti Anti
  deriving (Typeable, Data)

-- | Affine language type declarations
data TyDec' i
  -- | An abstract (empty) type
  = TdAbs {
      tdName      :: TypId i,
      tdParams    :: [TyVar i],
      -- | The variance of each parameter
      tdVariances :: [Variance],
      -- | Which the parameters guard equirecursion?
      tdGuards    :: [TyVar i],
      -- | Whether each parameter contributes to the qualifier
      tdQual      :: QExp i
    }
  -- | A type operator or synonym
  | TdSyn {
      tdName      :: TypId i,
      tdClauses   :: [([TyPat i], Type i)]
  }
  -- | An algebraic datatype
  | TdDat {
      tdName      :: TypId i,
      tdParams    :: [TyVar i],
      tdAlts      :: [(ConId i, Maybe (Type i))]
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
      ddv_   :: S.Set (QVarId i)
    }
  deriving (Typeable, Data)

instance Locatable (DeclNote i) where
  getLoc = dloc_

instance Relocatable (DeclNote i) where
  setLoc note loc = note { dloc_ = loc }

instance Notable (DeclNote i) where
  newNote = DeclNote bogus M.empty S.empty

newDecl :: Tag i => Decl' i -> Decl i
newDecl d0 = flip N d0 $ case d0 of
  DcLet p1 e2 ->
    newNote {
      dloc_  = getLoc (p1, e2),
      dfv_   = fv e2,
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
    newNote {
      dloc_  = getLoc me2,
      dfv_   = fv me2,
      ddv_   = S.mapMonotonic (\(J p n) -> J (u1:p) n) (qdv me2)
    }
  DcSig _ se2 ->
    newNote {
      dloc_  = getLoc se2
    }
  DcOpn me1 ->
    newNote {
      dloc_  = getLoc me1,
      dfv_   = fv me1,
      ddv_   = qdv me1
    }
  DcLoc ds1 ds2 ->
    newNote {
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

newModExp :: Tag i => ModExp' i -> ModExp i
newModExp me0 = flip N me0 $ case me0 of
  MeStr ds ->
    newNote {
      dloc_  = getLoc ds,
      dfv_   = fv ds,
      ddv_   = qdv ds
    }
  MeName _ qls ->
    newNote {
      ddv_  = S.fromList qls
    }
  MeAsc me se ->
    newNote {
      dloc_  = getLoc (me, se),
      dfv_   = fv me,
      ddv_   = qdv se
    }
  MeAnti a ->
    newNote {
      dfv_  = antierror "fv" a,
      ddv_  = antierror "dv" a
    }

newSigItem :: Tag i => SigItem' i -> SigItem i
newSigItem d0 = flip N d0 $ case d0 of
  SgVal l1 t2 ->
    newNote {
      dloc_  = getLoc t2,
      ddv_   = S.singleton (J [] l1)
    }
  SgTyp tds ->
    newNote {
      dloc_  = getLoc tds
    }
  SgMod u1 se2 ->
    newNote {
      dloc_  = getLoc se2,
      ddv_   = S.mapMonotonic (\(J p n) -> J (u1:p) n) (qdv se2)
    }
  SgSig _ se2 ->
    newNote {
      dloc_  = getLoc se2
    }
  SgInc se1 ->
    newNote {
      dloc_  = getLoc se1,
      ddv_   = qdv se1
    }
  SgExn _ t2 ->
    newNote {
      dloc_  = getLoc t2
    }
  SgAnti a ->
    newNote {
      dfv_  = antierror "fv" a,
      ddv_  = antierror "dv" a
    }

newSigExp :: Tag i => SigExp' i -> SigExp i
newSigExp se0 = flip N se0 $ case se0 of
  SeSig sis ->
    newNote {
      dloc_  = getLoc sis,
      ddv_   = qdv sis
    }
  SeName _ qls ->
    newNote {
      ddv_  = S.fromList qls
    }
  SeWith se1 _ _ t3 ->
    newNote {
      dloc_ = getLoc (se1, t3),
      ddv_  = qdv se1
    }
  SeAnti a ->
    newNote {
      dfv_  = antierror "fv" a,
      ddv_  = antierror "dv" a
    }

instance Tag i => Fv (N (DeclNote i) a) i where fv  = dfv_ . noteOf
instance Tag i => Dv (N (DeclNote i) a) i where qdv = ddv_ . noteOf

deriveNotable 'newDecl    (''Tag, [0]) ''Decl
deriveNotable 'newModExp  (''Tag, [0]) ''ModExp
deriveNotable 'newSigItem (''Tag, [0]) ''SigItem
deriveNotable 'newSigExp  (''Tag, [0]) ''SigExp
deriveNotable ''AbsTy
deriveNotable ''TyDec
deriveNotable ''Prog

---
--- Syntax Utils
---

-- | Turn a program into a sequence of declarations by replacing
-- the final expression with a declaration of variable 'it'.
prog2decls :: Tag i => Prog i -> [Decl i]
prog2decls (N _ (Prog ds (Just e)))
  = ds ++ [dcLet (paVar (ident "it")) e]
prog2decls (N _ (Prog ds Nothing))
  = ds

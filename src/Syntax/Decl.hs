{-# LANGUAGE
      DeriveDataTypeable #-}
module Syntax.Decl (
  -- * Declarations
  Decl(..), DeclT,
  -- ** Type declarations
  TyDec(..), AbsTy,
  TyDecT, AbsTyT,
  -- ** Modules
  ModExp(..), ModExpT,
  -- ** Synthetic consructors
  -- | These fill in the source location fields with a bogus location
  dcLet, dcTyp, dcAbs, dcMod, dcOpn, dcLoc, dcExn,

  -- * Programs
  Prog(..), ProgT,
  prog2decls
) where

import Loc as Loc
import Syntax.Anti
import Syntax.Kind
import Syntax.Ident
import Syntax.Type
import Syntax.Patt
import Syntax.Expr

import Data.Generics (Typeable(..), Data(..))

-- | A program is a sequence of declarations, maybe followed by an
-- expression
data Prog i = Prog [Decl i] (Maybe (Expr i))
  deriving (Typeable, Data)

-- | Declarations
data Decl i
  -- | Constant declaration
  = DcLet Loc Patt (Maybe (Type i)) (Expr i)
  -- | Type declaration
  | DcTyp Loc [TyDec i]
  -- | Abstype block declaration
  | DcAbs Loc [AbsTy i] [Decl i]
  -- | Module declaration
  | DcMod Loc Uid (ModExp i)
  -- | Module open
  | DcOpn Loc (ModExp i)
  -- | Local block
  | DcLoc Loc [Decl i] [Decl i]
  -- | Exception declaration
  | DcExn Loc Uid (Maybe (Type i))
  -- | Antiquote
  | DcAnti Anti
  deriving (Typeable, Data)

-- | Build a constant declaration with bogus source location
dcLet :: Patt -> Maybe (Type i) -> Expr i -> Decl i
dcLet  = DcLet bogus

-- | Build a type declaration with bogus source location
dcTyp :: [TyDec i] -> Decl i
dcTyp  = DcTyp bogus

-- | Build a abstype declaration with bogus source location
dcAbs :: [AbsTy i] -> [Decl i] -> Decl i
dcAbs  = DcAbs bogus

-- | Build a module with bogus source location
dcMod :: Uid -> ModExp i -> Decl i
dcMod  = DcMod bogus

-- | Build an open declaration with bogus source location
dcOpn :: ModExp i -> Decl i
dcOpn  = DcOpn bogus

-- | Build local block with bogus source location
dcLoc :: [Decl i] -> [Decl i] -> Decl i
dcLoc  = DcLoc bogus

-- | Build an exception declaration with bogus source location
dcExn :: Uid -> Maybe (Type i) -> Decl i
dcExn  = DcExn bogus

-- | Affine language type declarations
data TyDec i
  -- | An abstract (empty) type
  = TdAbs {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    -- | The variance of each parameter
    tdaVariances :: [Variance],
    -- | Whether each parameter contributes to the qualifier
    tdaQual      :: [Either TyVar Q]
  }
  -- | A type synonym
  | TdSyn {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaRHS       :: Type i
  }
  -- | An algebraic datatype
  | TdDat {
    tdaName      :: Lid,
    tdaParams    :: [TyVar],
    tdaAlts      :: [(Uid, Maybe (Type i))]
  }
  deriving (Typeable, Data)

-- | An abstract type in language A needs to specify variances
-- and the qualifier
type AbsTy i = ([Variance], [Either TyVar Q], TyDec i)

-- | A module expression
data ModExp i
  -- | A module literal
  = MeStr [Decl i]
  -- | A module variable
  | MeName QUid
  -- | An antiquote
  | MeAnti Anti
  deriving (Typeable, Data)

-- | A type-checked abstype declaration (has tycon info)
type AbsTyT   = AbsTy TyTag
-- | A type-checked type declaration (has tycon info)
type TyDecT   = TyDec TyTag
-- | A type-checked declaration (has tycon info)
type DeclT    = Decl TyTag
-- | A type-checked module expression (has tycon info)
type ModExpT  = ModExp TyTag
-- | A type-checked program (has tycon info)
type ProgT    = Prog TyTag

-----
----- Some classes and instances
-----

instance Locatable (Decl i) where
  getLoc (DcLet loc _ _ _) = loc
  getLoc (DcTyp loc _)     = loc
  getLoc (DcAbs loc _ _)   = loc
  getLoc (DcMod loc _ _)   = loc
  getLoc (DcOpn loc _)     = loc
  getLoc (DcLoc loc _ _)   = loc
  getLoc (DcExn loc _ _)   = loc
  getLoc (DcAnti a)        = antierror "getLoc" a

instance Relocatable (Decl i) where
  setLoc (DcLet _ n t e) loc = DcLet loc n t e
  setLoc (DcTyp _ td)    loc = DcTyp loc td
  setLoc (DcAbs _ at ds) loc = DcAbs loc at ds
  setLoc (DcMod _ m b)   loc = DcMod loc m b
  setLoc (DcOpn _ m)     loc = DcOpn loc m
  setLoc (DcLoc _ d d')  loc = DcLoc loc d d'
  setLoc (DcExn _ u e)   loc = DcExn loc u e
  setLoc (DcAnti a)      _   = DcAnti a

---
--- Syntax Utils
---

-- | Turn a program into a sequence of declarations by replacing
-- the final expression with a declaration of variable 'it'.
prog2decls :: Prog i -> [Decl i]
prog2decls (Prog ds (Just e))
  = ds ++ [DcLet (getLoc e) (PaVar (Lid "it")) Nothing e]
prog2decls (Prog ds Nothing)
  = ds


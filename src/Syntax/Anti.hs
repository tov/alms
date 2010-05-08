{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      QuasiQuotes,
      RankNTypes,
      TemplateHaskell,
      TypeFamilies,
      TypeOperators #-}
module Syntax.Anti (
  -- * Representation of antiquotes
  Anti(..),
  -- ** Raising errors when encountering antiquotes
  AntiFail(..), AntiError(..),
  -- * Generic anti projection/injection
  Antible(..),
  deriveAntible, deriveAntibleType,
  (!!!),
  -- * Antiquote expansion
  -- ** Generic expander construction
  AntiDict,
  expandAnti, expandAntible, expandAntible1,
  expandAntiFun, expandAntibleType,
  -- ** Antiquote dictionaries for various non-terminals
  litAntis, pattAntis,
  exprAntis, bindingAntis, caseAltAntis,
  typeAntis, quantAntis, tyTagAntis, qExpAntis, tyVarAntis,
  declAntis, tyDecAntis, absTyAntis, modExpAntis,
  lidAntis, uidAntis, qlidAntis, quidAntis, idAntis,
  noAntis, optAntis, listAntis, maybeAntis
) where

import Loc (fromTHLoc)
import Syntax.THQuasi
import {-# SOURCE #-} Syntax.Type

import Data.Generics (Typeable, Data, extQ)
import qualified Data.Map as M
import Language.Haskell.TH as TH

--
-- Representation of antiquotes
--

data Anti = Anti {
              anType :: String,
              anName :: String
            }
  deriving (Eq, Ord, Typeable, Data)

instance Show Anti where
  show (Anti ""   aid) = '$' : aid
  show (Anti atag aid) = '$' : atag ++ ':' : aid

class AntiFail a where
  antifail :: a

instance Monad m => AntiFail (String -> Anti -> m b) where
  antifail who what = fail $
    "BUG! " ++ who ++ ": encountered antiquote " ++ show what

instance AntiFail (Name -> TH.ExpQ) where
  antifail a = do
    loc <- TH.location
    [| antifail $(stringE (show (fromTHLoc loc))) $(varE a) |]

instance AntiFail (TH.Q TH.Exp) where
  antifail = antifail (mkName "a")

class AntiError a where
  antierror :: a

instance AntiError (String -> Anti -> b) where
  antierror who what = error $
    "BUG! " ++ who ++ ": encountered antiquote " ++ show what

instance AntiError (Name -> TH.ExpQ) where
  antierror a = do
    loc <- TH.location
    [| antierror $(stringE (show (fromTHLoc loc))) $(varE a) |]

instance AntiError (TH.Q TH.Exp) where
  antierror = antierror (mkName "a")

class Antible a where
  injAnti     :: Anti -> a
  prjAnti     :: a -> Maybe Anti
  dictOf      :: a -> AntiDict

  injAntiList :: Anti -> [a]
  prjAntiList :: [a] -> Maybe Anti
  dictOfList  :: [a] -> AntiDict

  injAntiList     = return . injAnti
  prjAntiList [a] = prjAnti a
  prjAntiList _   = Nothing
  dictOfList      = const listAntis

instance Antible a => Antible [a] where
  injAnti = injAntiList
  prjAnti = prjAntiList
  dictOf  = dictOfList

instance Antible a => Antible (Maybe a) where
  injAnti = return . injAnti
  prjAnti = (prjAnti =<<)
  dictOf  = const optAntis

(!!!) :: Antible a => a -> String -> a
stx !!! msg = case prjAnti stx of
  Nothing -> stx
  Just a  -> antierror msg a

-- Given the name of the constructor for storing Anti and the name
-- of an antiquote dictionary, generate an instance of Antible
deriveAntible :: TH.Name -> TH.Name -> TH.Q [TH.Dec]
deriveAntible con = deriveAntibleType (resType =<< reify con) con
  where
  resType (TH.DataConI _ t0 _ _) = loop t0 where
    loop (TH.ForallT _ _ t) = loop t
    loop (TH.AppT (TH.AppT TH.ArrowT _) t) = return t
    loop _  = fail $ "deriveAntible: `" ++ show con ++ "' does not " ++
                     "have exactly one argument"
  resType _ = fail $ "deriveAntible: `" ++ show con ++
                     "' is not a data constructor"

-- Like deriveAntibleType, but requires the type for the instance
-- to declare as well.
deriveAntibleType :: TH.TypeQ -> TH.Name -> TH.Name -> TH.Q [TH.Dec]
deriveAntibleType typ con dict =
  [d| instance Antible $typ where
        injAnti     = $(conE con)
        prjAnti stx = $(caseE [| stx |] [
                          match (conP con [varP a])
                                (normalB [| Just $(varE a) |])
                                [],
                          match wildP
                                (normalB [| Nothing |])
                                []
                       ])
        dictOf _    = $(varE dict)
        injAntiList     = return . injAnti
        prjAntiList [b] = prjAnti b
        prjAntiList _   = Nothing
        dictOfList      = const listAntis
  |]
  where
  a = mkName "a"

--
-- Antiquote table
--

-- | A pat/exp-generic parser
type PreTrans = forall b. ToSyntax b => String -> Q b
-- | A pat/exp-generic parser, wrapped
newtype Trans = Trans { unTrans :: PreTrans }
-- | A dictionary mapping antiquote tags to parsers
type AntiDict = M.Map String Trans

-- | Generate an antiquote expander given the name of the constructor
--   to match to extract antiquotes and the name of the dictionary
expandAnti    :: Name -> Name -> ExpQ
expandAnti     = expandAntiPrj [| id |]

-- | Generate an antiquote expander using the 'Antible' class
--   projection, given the name of a dictionary
expandAntible'   :: TypeQ -> Name -> ExpQ
expandAntible' _t = expandAntiPrj [| prjAnti:: $_t -> Maybe Anti |] 'Just

-- | Generate an antiquote expander, given the name of a projection
--   to get antiquotes out of things, a constructor to match them out,
--   and the name of a dictionary.
expandAntiPrj :: ExpQ -> Name -> Name -> ExpQ
expandAntiPrj prj con dict = do
  term <- newName "term"
  tag  <- newName "tag"
  name <- newName "name"
  lamE [varP term] $
    caseE [| $prj $(varE term) |] [
      match (conP con [conP 'Anti [varP tag, varP name]])
            (normalB [| case M.lookup $(varE tag) $(varE dict) of
                          Just tr -> Just (unTrans tr $(varE name))
                          Nothing -> Nothing {- Just $ fail $
                            "unknown antiquote `" ++ $(varE tag) ++
                            "' for dict " ++
                            $(litE (stringL (nameBase dict))) -}
                      |])
            [],
      match wildP
            (normalB [| Nothing |])
            []
    ]

expandAntible :: Name -> ExpQ
expandAntible name = do
  info <- reify name
  case info of
    TyConI (DataD _ _ [_] _ _)    -> expandAntible1 name
    TyConI (NewtypeD _ _ [_] _ _) -> expandAntible1 name
    _                             -> expandAntible0 name

expandAntible0 :: Name -> ExpQ
expandAntible0 name =
  [| $(expandAntibleType [t| $_t |]) |]
  where _t = conT name

expandAntible1 :: Name -> ExpQ
expandAntible1 name = 
  [| $(expandAntibleType [t| $_t () |])
   . $(expandAntibleType [t| $_t TyTag |]) |]
  where _t = conT name

expandAntibleType :: TypeQ -> ExpQ
expandAntibleType _t =
  [| (`extQ` (\x -> expandAntiFun (x:: $_t)))
   . (`extQ` (\x -> expandAntiFun (x:: Maybe $_t)))
   . (`extQ` (\x -> expandAntiFun (x:: [$_t]))) |]

expandAntiFun :: (Antible a, ToSyntax b) => a -> Maybe (Q b)
expandAntiFun stx = do
  Anti tag name <- prjAnti stx
  trans         <- M.lookup tag (dictOf stx)
  return (unTrans trans name)

-- | Construct a singleton antiquote dictionary from a key and
--   generic parser
(=:) :: String -> PreTrans -> AntiDict
a =: b = M.singleton a (Trans b)
infix 2 =:

-- | Concatenate antiquote dictionaries
(&) :: AntiDict -> AntiDict -> AntiDict
(&)  = M.union
infixl 1 &

litAntis, pattAntis,
  exprAntis, bindingAntis, caseAltAntis,
  typeAntis, quantAntis, tyTagAntis, qExpAntis, tyVarAntis,
  declAntis, tyDecAntis, absTyAntis, modExpAntis,
  lidAntis, uidAntis, qlidAntis, quidAntis, idAntis,
  noAntis, optAntis, listAntis, maybeAntis
    :: AntiDict

litAntis   = "lit"   =: [$th| <_> |]
           & "str"   =: [$th| LtStr <_> |]
           & "int"   =: [$th| LtInt <_> |]
           & "flo"   =: [$th| LtFloat <_> |]
           & "float" =: [$th| LtFloat <_> |]
           & "antiL" =: [$th| LtAnti <_> |]

pattAntis  = ""      =: [$th| <_> |]
           & "patt"  =: [$th| <_> |]
           & "anti"  =: [$th| PaAnti <_> |]

exprAntis  = ""      =: [$th| <_> |]
           & "expr"  =: [$th| <_> |]
           & "id"    =: [$th| exId <_>
                            | Expr { expr_ = ExId <_> } |]
           & "expr_" =: [$th| expr__tag_for_patterns_only
                            | Expr { expr_ = <_> } |]
           & "anti"  =: [$th| exAnti <_>
                            | Expr { expr_ = ExAnti <_> } |]
bindingAntis
           = ""      =: [$th| <_> |]
           & "bind"  =: [$th| <_> |]
           & "anti"  =: [$th| BnAnti <_> |]
caseAltAntis
           = "case"  =: [$th| <_> |]
           & "caseA" =: [$th| CaAnti <_> |]

typeAntis  = ""      =: [$th| <_> |]
           & "type"  =: [$th| <_> |]
           & "anti"  =: [$th| TyAnti <_> |]

quantAntis = "quant" =: [$th| <_> |]
           & "antiQ" =: [$th| QuAnti <_> |]

tyTagAntis = ""      =: [$th| <_> |]
           & "tytag" =: [$th| <_> |]
           & "td"    =: (\v -> case getTdByName v of
                           Nothing -> fail $
                             "Unrecognized type name: " ++ v
                           Just td -> dataS td)
           & "anti"  =: [$th| TyTagAnti <_> |]

qExpAntis  = ""      =: [$th| <_> |]
           & "qexp"  =: [$th| <_> |]
           & "qlit"  =: [$th| QeLit <_> |]
           & "qvar"  =: [$th| QeVar <_> |]
           & "qdisj" =: [$th| qeDisj <_> | QeDisj <_> |]
           & "qconj" =: [$th| qeConj <_> | QeConj <_> |]
           & "anti"  =: [$th| QeAnti <_> |]

tyVarAntis = ""      =: [$th| <_> |]
           & "tyvar" =: [$th| <_> |]

declAntis  = ""      =: [$th| <_> |]
           & "decl"  =: [$th| <_> |]
           & "anti"  =: [$th| DcAnti <_> |]

tyDecAntis = ""      =: [$th| <_> |]
           & "tydec" =: [$th| <_> |]
           & "anti"  =: [$th| TdAnti <_> |]

absTyAntis = ""      =: [$th| <_> |]
           & "absty" =: [$th| <_> |]
           & "anti"  =: [$th| AbsTyAnti <_> |]

modExpAntis= ""      =: [$th| <_> |]
           & "mod"   =: [$th| <_> |]
           & "anti"  =: [$th| MeAnti <_> |]

lidAntis   = "lid"   =: [$th| <_> |]
           & "name"  =: [$th| Lid <_> |]
uidAntis   = "uid"   =: [$th| <_> |]
           & "uname" =: [$th| Uid <_> |]
qlidAntis  = "qlid"  =: [$th| <_> |]
           & "qname" =: [$th| qlid <_> |] -- error in pattern context
quidAntis  = "quid"  =: [$th| <_> |]
           & "quname"=: [$th| quid <_> |] -- error in pattern context
idAntis    = "id"    =: [$th| <_> |]

noAntis    = M.empty

optAntis   = "opt"   =: [$th| <_> |]
           & "some"  =: [$th| Just <_> |]
           & "none"  =: const [$th| Nothing |]

listAntis  = "list"  =: [$th| <_> |]
           & "nil"   =: const [$th| [ ] |]
           & "list1" =: [$th| [ <_> ] |]

maybeAntis = optAntis & listAntis

-- DcLet _ _ MaybeType _
-- DcType _ ListTyDec
-- DcAbs _ ListAbsTy ListDecl
-- DcLoc _ ListDecl ListDecl
-- DcExn _ _ MaybeType
-- MeStr ListDecl
-- ExCase _ ListCaseAlt
-- ExLetRec ListBinding _
-- ExPack MaybeType _ _
-- ExCast _ MaybeType _
-- PaCon _ MaybePatt _
-- TyCon _ ListType _
-- BnAnti
-- CaAnti
-- TdAnti
-- AbsTyAnti

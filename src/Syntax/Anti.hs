{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleContexts,
      FlexibleInstances,
      PatternGuards,
      RankNTypes,
      TemplateHaskell #-}
module Syntax.Anti (
  -- * Representation of antiquotes
  Anti(..),
  -- ** Raising errors when encountering antiquotes
  AntiFail(..), AntiError(..),
  -- * Generic anti projection/injection
  Antible(..), deriveAntibles,
  -- * Generic location expansion
  LocAst(..), deriveLocAsts,
  -- * Antiquote expansion
  -- ** Generic expander construction
  expandAntibles, expandAntible, expandAntibleType,
  -- * Syntax classes and antiquote tables
  -- ** Antiquote tables
  -- *** Types
  AntiDict, PreTrans, Trans(..),
  -- *** Constructors
  (=:), (=:!), (=:<), (&),
  -- ** Syntax classs
  -- *** Types
  SyntaxClass(..), SyntaxTable,
  -- *** Constructors
  (=::), ($:), (!:), (>:)
) where

import Loc as Loc
import Meta.THHelpers
import Syntax.Notable
import Util

import Data.Generics (Typeable, Data, extQ)
import Data.List (elemIndex)
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

optAntis, listAntis :: AntiDict

listAntis 
  = "list"  =:  Nothing
  & "nil"   =:  Just (\_ -> conS '[] [])
  & "list1" =:  Just (\v -> listS [varS (TH.mkName v) []])

optAntis
  = "opt"   =:  Nothing
  & "some"  =:< 'Just
  & "none"  =:  Just (\_ -> conS 'Nothing [])

---
--- Deriving antiquotes
---

-- Given the syntax table, we need to derive instances of Antible
-- and antiquoters
deriveAntibles :: SyntaxTable -> TH.Q [TH.Dec]
deriveAntibles  = concatMapM each where
  each SyntaxClass { scDict = Nothing } = return []
  each sc@SyntaxClass { scDict = Just dict } = do
    TH.TyConI tc <- reify (scName sc)
    (cxt, tvs) <- case tc of
      TH.DataD cxt _ tvs _ _    -> return (cxt, tvs)
      TH.NewtypeD cxt _ tvs _ _ -> return (cxt, tvs)
      TH.TySynD _ tvs _         -> return ([], tvs)
      _ -> fail "deriveAntibles requires type"
    a <- TH.newName "a"
    let wrapper p = case scWrap sc of
          Nothing -> p
          Just _  -> TH.conP 'N [TH.wildP, p]
    [InstanceD context head decs] <-
      [d| instance Antible $(foldl TH.appT (TH.conT (scName sc))
                                   (map typeOfTyVarBndr tvs)) where
            injAnti     = $(varE (maybe 'id id (scWrap sc)))
                        . $(conE (scAnti sc))
            prjAnti stx = $(caseE [| stx |] [
                              match (wrapper (TH.conP (scAnti sc) [TH.varP a]))
                                    (TH.normalB [| Just $(TH.varE a) |])
                                    [],
                              match TH.wildP
                                    (TH.normalB [| Nothing |])
                                    []
                           ])
            dictOf _    = $(varE dict)
            injAntiList     = return . injAnti
            prjAntiList [b] = prjAnti b
            prjAntiList _   = Nothing
            dictOfList      = const listAntis
        |]
    context' <- buildContext tvs (scCxt sc)
    return [InstanceD (context' ++ context) head decs]

--
-- Location expanders
--

class LocAst stx where
  toLocAstQ :: ToSyntax ast => TH.Name -> stx -> TH.Q ast

deriveLocAst :: Name -> SyntaxClass -> TH.Q [TH.Dec]
deriveLocAst _     SyntaxClass { scWrap = Nothing } = return []
deriveLocAst build SyntaxClass { scName = name, scCxt = cxt } = do
  info <- reify name
  case info of
    -- Located t i
    TyConI (TySynD _ _ (AppT (AppT _ (ConT _)) _)) ->
      thenNote ''LocNote
    -- N (note i) (t i)
    TyConI (TySynD _ _ (AppT (AppT _ (AppT (ConT note) _))
                             (AppT (ConT _) _))) ->
      thenNote note
    _ -> return []
  where
  --
  thenNote note = do
    info <- reify note
    case info of
      TyConI (DataD _ _ _ [con] _)  -> thenCon con
      TyConI (NewtypeD _ _ _ con _) -> thenCon con
      _ -> runIO (print (name, info)) >> return []
  --
  thenCon (ForallC _ _ con)     = thenCon con
  thenCon (InfixC st1 dcon st2) = thenDCon dcon [snd st1, snd st2]
  thenCon (NormalC dcon sts)    = thenDCon dcon (map snd sts)
  thenCon (RecC dcon vsts)      = thenDCon dcon [t | (_,_,t) <- vsts]
  --
  thenDCon dcon ts
    | Just ix <- elemIndex (ConT ''Loc.Loc) ts = do
      i <- newName "i"
      [InstanceD [] head decls] <-
        [d| instance LocAst ($(conT name) $(varT i)) where
              toLocAstQ loc stx =
                do
                  let _ignore = $(stringE (show name))
                  ast <- $(varE build) stx
                  case ast of
                    VarE _ -> return ast
                    _      -> varS $(stringE (show 'setLoc))
                                   [return ast, varS loc []]
                `whichS'`
                do
                  let pat preAstQ =
                        conS $(stringE (show 'N))
                            [ conS $(stringE (show dcon))
                                   $(listE [ if i == ix
                                               then [| varS loc [] |]
                                               else [| wildS |]
                                           | i <- [0 .. length ts - 1] ])
                            , preAstQ ]
                  ast <- $(varE build) stx
                  case ast of
                    VarP v -> asP v (pat wildP)
                    ConP _ [_, preAst] -> pat (return preAst)
                    _ -> fail $
                      "BUG! toLocAstQ did not recognize " ++
                      "expanded code: " ++ show ast
          |]
      context' <- buildContext [PlainTV i] ((''Data, [0]) : cxt)
      return [InstanceD context' head decls]
    | otherwise = return []

deriveLocAsts :: Name -> SyntaxTable -> TH.Q [TH.Dec]
deriveLocAsts name = concatMapM (deriveLocAst name)

--
-- Antiquote expanders
--

expandAntibles :: [Name] -> Name -> SyntaxTable -> ExpQ
expandAntibles params name = foldr each [| id |] where
  each sc rest = [| $(expandAntible params name sc) . $rest |]

expandAntible :: [Name] -> Name -> SyntaxClass -> ExpQ
expandAntible params build SyntaxClass { scName = name, scWrap = wrap } = do
  info <- reify name
  case info of
    TyConI (DataD _ _ [_] _ _)    -> expandAntible1 params build wrap name
    TyConI (NewtypeD _ _ [_] _ _) -> expandAntible1 params build wrap name
    TyConI (TySynD _ [_] _)       -> expandAntible1 params build wrap name
    _                             -> expandAntible0 build wrap name

expandAntible0 :: Name -> Maybe Name -> Name -> ExpQ
expandAntible0 build maybeWrap typeName =
  [| $(expandAntibleType build maybeWrap [t| $_t |]) |]
  where _t = conT typeName

expandAntible1 :: [Name] -> Name -> Maybe Name -> Name -> ExpQ
expandAntible1 params build maybeWrap typeName =
  foldr (\a b -> [| $a . $b |]) [| id |]
    [ expandAntibleType build maybeWrap [t| $_t $(conT _p) |]
    | _p <- params ]
  where _t = conT typeName

expandAntibleType :: Name -> Maybe Name -> TypeQ -> ExpQ
expandAntibleType build maybeWrap _t =
  let main = case maybeWrap of
        Nothing  ->
          [| \x -> expandAntiFun (x:: $_t) |]
        Just wrap ->
          [| \x -> expandWrappedAntiFun
                     $(varE build)
                     (mkName $(stringE (show wrap)))
                     (x:: $_t) |]
   in
  [| (`extQ` $main)
   . (`extQ` (\x -> expandAntiFun (x:: Maybe $_t)))
   . (`extQ` (\x -> expandAntiFun (x:: [$_t]))) |]

expandWrappedAntiFun :: (Antible (N note a), ToSyntax b) =>
                        (a -> Q b) -> Name -> N note a -> Maybe (Q b)
expandWrappedAntiFun build wrap stx =
  Just $ case prjAnti stx of
    Just (Anti tag name) -> case M.lookup tag (dictOf stx) of
      Just (Trans trans)   -> case trans of
        Just f               -> doWrap (f name)
        Nothing              -> varS name []
      Nothing              -> fail $
        "Unrecognized antiquote tag: `" ++ tag ++ "'"
    Nothing              -> doWrap (build (dataOf stx))
  where
  doWrap preStx = varS wrap [preStx] `whichS` conS 'N [wildS, preStx]

expandAntiFun :: (Antible a, ToSyntax b) => a -> Maybe (Q b)
expandAntiFun stx = do
  Anti tag name <- prjAnti stx
  case M.lookup tag (dictOf stx) of
    Just trans -> return $ case unTrans trans of
      Just f     -> f name
      Nothing    -> varS name []
    Nothing    -> fail $ "Unrecognized antiquote tag: `" ++ tag ++ "'"

--
-- Antiquote and syntax table
--

-- | A pat/exp-generic parser
type PreTrans = forall b. ToSyntax b => Maybe (String -> Q b)
-- | A pat/exp-generic parser, wrapped
newtype Trans = Trans { unTrans :: PreTrans }
-- | A dictionary mapping antiquote tags to parsers
type AntiDict = M.Map String Trans

-- | A descriptor for a syntactic category, used for generating
--   antiquotes
data SyntaxClass = SyntaxClass {
  scName    :: Name,
  -- | The name of the constructor for antiquotes
  scAnti    :: Name,
  -- | The safe injection from the underlying type to the main type
  scWrap    :: Maybe Name,
  -- | The dictionary of splice tags
  scDict    :: Maybe Name,
  -- | Type class context required for wrapping
  scCxt     :: [(Name, [Int])]
}

type SyntaxTable = [SyntaxClass]

-- | Construct a single syntax class from the type name and antiquote
--   constructor
(=::) :: TH.Name -> TH.Name -> SyntaxClass
name =:: anti = SyntaxClass {
  scName   = name,
  scAnti   = anti,
  scWrap   = Nothing,
  scDict   = Nothing,
  scCxt    = []
}

-- | Extend a syntax class with the name of a function that lifts
--   from pre-syntax to syntax
(!:) :: SyntaxClass -> TH.Name -> SyntaxClass
tab !: name = tab { scWrap = Just name }

-- | Extend a syntax class with the name of an antiquote dictionary
($:) :: SyntaxClass -> TH.Name -> SyntaxClass
tab $: dict = tab { scDict = Just dict }

-- | Extend a syntax class with a context
(>:) :: SyntaxClass -> (Name, [Int]) -> SyntaxClass
tab >: cxt  = tab { scCxt = cxt : scCxt tab }

infixl 2 =::, !:, $:, >:

-- | Append two antiquote dictionaries
(&) :: AntiDict -> AntiDict -> AntiDict
(&)  = M.union

infixr 1 &

-- | Construct a singleton antiquote dictionary from a key and
--   generic parser
(=:) :: String -> PreTrans -> AntiDict
a =: b = M.singleton a (Trans b)

-- | Create singleton dictionary with default (tagless) entry
(=:!)  :: String -> PreTrans -> AntiDict
a =:! b = M.union ("" =: b) (a =: b)

-- | Construct an antiquote dictionary for matching a
--   simple constructor
(=:<) :: String -> TH.Name -> AntiDict
a =:< n  = a =: Just (\v -> conS n [varS v []])

infix 2 =:, =:!, =:<


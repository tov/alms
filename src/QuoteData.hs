---
--- My verson of Language.Haskell.TH.Quote
---
{-# LANGUAGE
      RankNTypes,
      ScopedTypeVariables #-}
module QuoteData (dataToExpQ, dataToPatQ) where

import Language.Haskell.TH
import Data.Data

dataToQa  ::  forall a k q. Data a
          =>  (Name -> k)
          ->  (Lit -> Q q)
          ->  (k -> [Q q] -> Q q)
          ->  (forall b . Data b => b -> Maybe (Q q))
          ->  [(String, String)]
          ->  a
          ->  Q q
dataToQa mkCon mkLit appCon antiQ quals t =
    case antiQ t of
      Nothing ->
          case constrRep constr of
            AlgConstr _  ->
                appCon con conArgs
            IntConstr n ->
                mkLit $ integerL n
            FloatConstr n ->
                mkLit $ rationalL (toRational n)
            CharConstr c ->
                mkLit $ charL c
        where
          constr :: Constr
          constr = toConstr t
          constrName :: Constr -> String
          constrName k =
            qual k $
              case showConstr k of
                name@('(':',':_) -> name
                '(':name         -> init name
                name             -> name
          qual :: Constr -> String -> String
          qual k =
            let modname = tyconModule (dataTypeName (constrType k)) in
              case lookup modname quals of
                Nothing -> id
                Just s  -> ((s ++ ".") ++)
          con :: k
          con = mkCon (mkName (constrName constr))
          conArgs :: [Q q]
          conArgs = gmapQ (dataToQa mkCon mkLit appCon antiQ quals) t

      Just y -> y

-- | 'dataToExpQ' converts a value to a 'Q Exp' representation of the same
-- value. It takes a function to handle type-specific cases.
dataToExpQ  ::  Data a
            =>  (forall b . Data b => b -> Maybe (Q Exp))
            ->  [(String, String)]
            ->  a
            ->  Q Exp
dataToExpQ = dataToQa conE litE (foldl appE)

-- | 'dataToPatQ' converts a value to a 'Q Pat' representation of the same
-- value. It takes a function to handle type-specific cases.
dataToPatQ  ::  Data a
            =>  (forall b . Data b => b -> Maybe (Q Pat))
            ->  [(String, String)]
            ->  a
            ->  Q Pat
dataToPatQ = dataToQa id litP conP

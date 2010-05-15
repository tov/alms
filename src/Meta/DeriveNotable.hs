{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      TemplateHaskell #-}
module Meta.DeriveNotable (
  deriveNotable
) where

import Syntax.Notable
import Meta.THHelpers

import Data.Char (toLower)
import Language.Haskell.TH

data DeriveNotableRec
  = DeriveNotableRec {
      dnFrom       :: Maybe Name,
      dnBy         :: Name,
      dnExcept     :: [Name]
    }

class ExtDN a r where
  extDN :: DeriveNotableRec -> a -> r
instance ExtDN Name (Q [Dec]) where
  extDN dn = deriveNotableBEF (dnBy dn) (dnExcept dn) (dnFrom dn)
instance ExtDN a r => ExtDN (Maybe Name) (a -> r) where
  extDN dn mn = extDN (dn { dnFrom = mn })
instance ExtDN a r => ExtDN Name (a -> r) where
  extDN dn n = extDN (dn { dnBy = n })
instance ExtDN a r => ExtDN [Name] (a -> r) where
  extDN dn ns = extDN (dn { dnExcept = ns })

deriveNotable :: ExtDN a r => a -> r
deriveNotable = extDN DeriveNotableRec {
  dnBy     = 'newN,
  dnExcept = [],
  dnFrom   = Nothing
}

deriveNotableBEF :: Name -> [Name] -> Maybe Name -> Name -> Q [Dec]
deriveNotableBEF new except fromName toName = do
  TyConI tc <- case fromName of
    Just n  -> reify n
    Nothing -> do
      TyConI (TySynD _ _ fromType) <- reify toName
      case fromType of
        AppT (AppT _ (AppT _ _)) (AppT (ConT n) _) -> reify n
        AppT (AppT _ (ConT n)) _                   -> reify n
        _ -> fail "deriveNotable: Can't find data type"
  case tc of
    DataD context _ tvs cons _   -> go except new toName context tvs cons
    NewtypeD context _ tvs con _ -> go except new toName context tvs [con]
    _ -> fail "deriveNotable supports data and newtype only"

go :: [Name] -> Name -> Name -> Cxt -> [TyVarBndr] -> [Con] -> Q [Dec]
go except new toName context tvs cons = do
  let rtype = foldl appT (conT toName) (map typeOfTyVarBndr tvs)
      quant = forallT tvs (return context)
  declses <- sequence [ deriveOne new quant rtype con 
                      | con <- cons,
                        conName con `notElem` except ]
  return (concat declses)

deriveOne :: Name -> (TypeQ -> TypeQ) -> TypeQ -> Con -> Q [Dec]
deriveOne new quant rtype (NormalC cname params0) = do
  let ptypes  = map (return . snd) params0
      funName = mkName (lowerFirst (nameBase cname))
  params <- mapM (newName . const "x") params0
  prot   <- sigD funName (quant (foldr (\ _tj _tr -> [t| $_tj -> $_tr |])
                                       rtype ptypes))
  decl   <- funD funName
    [
      clause (map varP params)
             (normalB
              (appE (varE new)
                    (foldl appE (conE cname) (map varE params))))
             []
    ]
  return [prot, decl]
deriveOne new tvs rtype (RecC cname params) =
  deriveOne new tvs rtype (NormalC cname [ (s, t) | (_, s, t) <- params ])
deriveOne new tvs rtype (InfixC st1 cname st2) =
  deriveOne new tvs rtype (NormalC cname [st1, st2])
deriveOne new tvs rtype (ForallC _ _ con) = deriveOne new tvs rtype con

lowerFirst :: String -> String
lowerFirst ""     = ""
lowerFirst (c:cs) = toLower c : cs

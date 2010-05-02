-- | Converts coercion expressions to dynamic checks.
{-# LANGUAGE
      PatternGuards,
      QuasiQuotes #-}
module Coercion  (
  coerceExpression,
  translate, translateDecls, TEnv, tenv0
) where

import Loc
import Ppr ()
import Quasi
import Syntax
import TypeRel
import Util

import qualified Data.Map as M
import qualified Control.Monad.State as CMS

-- | The translation environment.  This currently doesn't carry
--   any information, but we keep it in the interface for later use.
type TEnv = ()

-- | The initial translation environment
tenv0 :: TEnv
tenv0  = ()

-- | Translate a whole program
translate :: TEnv -> ProgT -> ProgT
translate _ = id

-- | Translation a sequence of declarations in the context
--   of a translation environment, returning a new translation
--   environment
translateDecls :: TEnv -> [DeclT] -> (TEnv, [DeclT])
translateDecls tenv decls = (tenv, decls)

coerceExpression :: Monad m => ExprT -> TypeT -> TypeT -> m ExprT
coerceExpression e tfrom tto = do
  prj <- CMS.evalStateT (build M.empty tfrom tto) 0
  return $ exApp (exApp prj (exPair (exStr neg) (exStr pos))) e
  where
  neg = "context at " ++ show (getLoc e)
  pos = "value at " ++ show (getLoc e)

build :: Monad m =>
         M.Map (TyVar, TyVar) (Maybe Lid) -> TypeT -> TypeT ->
         CMS.StateT Integer m ExprT
build recs tfrom tto
  | (tvs,  [$ty|+ ($t1, $t2)   $qlid:_ $info  |]) <- unfoldTyQu Forall tfrom,
    (tvs', [$ty|+ ($t1', $t2') $qlid:_ $info' |]) <- unfoldTyQu Forall tto,
    length tvs == length tvs',
    info `elem` funtypes && info' `elem` funtypes,
    which <- "INTERNALS.Contract." ++
               if info == tdArr
                 then "func"
                 else if info' == tdArr
                   then "affunc"
                   else "funcA"
    = do
        let recs' = foldr2
                      M.insert
                      (shadow tvs tvs' recs)
                      (zip tvs tvs')
                      (repeat Nothing)
        dom <- build recs' t1' t1
        cod <- build recs' t2 t2'
        let body = exApp (exApp (exVar (qlid which)) dom) cod
        return $ if null tvs
          then body
          else absContract $
               exAbsVar' (Lid "f") tfrom $
               foldr (\tv0 acc -> exTAbs tv0 . acc) id tvs $
               exAbsVar' (Lid "x") t1' $
               instContract body `exApp`
               foldl (\acc tv0 -> exTApp acc (TyVar tv0))
                     (exBVar (Lid "f")) tvs `exApp`
               exBVar (Lid "x")
build recs (TyQu Exists tv t) (TyQu Exists tv' t') = do
  let recs' = M.insert (tv, tv') Nothing (shadow [tv] [tv'] recs)
  body <- build recs' t t' >>! instContract
  let tv''  = freshTyVar tv (ftv (tv, tv'))
  return $
    absContract $
      [$ex|+@! fun (Pack('$tv'', e) : ex '$tv . $t) ->
                 Pack[ex '$tv' . $t']('$tv'', $body e) |]
build recs (TyMu tv t) (TyMu tv' t') = do
  lid  <- freshLid
  let recs' = M.insert (tv, tv') (Just lid) (shadow [tv] [tv'] recs)
  body <- build recs' t t'
  return $
    [$ex|+@!
      let rec $lid:lid
              (parties : party $tdString * $tdTuple party $tdString)
                       : (mu '$tv . $t) -> $tdArr mu '$tv' . $t'
          = $body parties
       in $lid:lid
    |]
build recs (TyVar tv) (TyVar tv')
  | Just (Just lid) <- M.lookup (tv, tv') recs
    = return $ exBVar lid
build recs (TyVar tv) (TyVar tv')
  | Just Nothing <- M.lookup (tv, tv') recs
    = return $ exTApp (exVar (qlid "INTERNALS.Contract.any")) (TyVar tv')
build _ t t' =
  if t <: t'
    then return $ exTApp (exVar (qlid "INTERNALS.Contract.any")) t'
    else fail $ "No coercion from " ++ show t ++ " to " ++ show t'

shadow :: [TyVar] -> [TyVar] ->
          M.Map (TyVar, TyVar) a -> M.Map (TyVar, TyVar) a
shadow tvs tvs' = M.filterWithKey
                    (\(tv, tv') _ -> tv `notElem` tvs && tv' `notElem` tvs')

absContract :: ExprT -> ExprT
absContract  =
  exAbs (PaPair (PaVar (Lid "neg")) (PaVar (Lid "pos")))
        (tyTupleT tyPartyT tyPartyT)

instContract :: ExprT -> ExprT
instContract  =
  (`exApp` exPair (exBVar (Lid "neg")) (exBVar (Lid "pos")))

freshLid :: Monad m => CMS.StateT Integer m Lid
freshLid = do
  n <- CMS.get
  CMS.put (n + 1)
  return (Lid ("c" ++ show n))

tyPartyT :: TypeT
tyPartyT  = [$ty|+ INTERNALS.Contract.party $td:string |]


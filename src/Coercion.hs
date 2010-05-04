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

-- | Location to use for constructed code
_loc :: Loc
_loc  = mkBogus "<coercion>"

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
  | (tvs,  [$ty|+ $t1  -[$qe ]> $t2  |]) <- unfoldTyQu Forall tfrom,
    (tvs', [$ty|+ $t1' -[$qe']> $t2' |]) <- unfoldTyQu Forall tto,
    length tvs == length tvs'
    = do
        qd  <- qInterpretM qe
        qd' <- qInterpretM qe'
        let which = case (qConstBound qd, qConstBound qd') of
              (Qa, Qu) -> [$ex|+ INTERNALS.Contract.affunc |]
              (Qu, _ ) -> [$ex|+ INTERNALS.Contract.func[U] |]
              (_ , Qa) -> [$ex|+ INTERNALS.Contract.func[A] |]
            recs' = foldr2
                      M.insert
                      (shadow tvs tvs' recs)
                      (zip tvs tvs')
                      (repeat Nothing)
        dom <- build recs' t1' t1
        cod <- build recs' t2 t2'
        let body = [$ex|+ $which $dom $cod |]
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
build recs [$ty|+ ex '$tv. $t |] [$ty|+ ex '$tv'. $t' |] = do
  let recs' = M.insert (tv, tv') Nothing (shadow [tv] [tv'] recs)
  body <- build recs' t t' >>! instContract
  let tv''  = freshTyVar tv (ftv (tv, tv'))
  return $
    absContract $
      [$ex|+ fun (Pack('$tv'', e) : ex '$tv. $t) ->
               Pack[ex '$tv'. $t']('$tv'', $body e) |]
build recs [$ty|+ mu '$tv. $t |] [$ty|+ mu '$tv'. $t' |] = do
  lid  <- freshLid
  let recs' = M.insert (tv, tv') (Just lid) (shadow [tv] [tv'] recs)
  body <- build recs' t t'
  return $
    [$ex|+
      let rec $lid:lid
              (parties : string $td:string * $td:tuple string $td:string)
                       : (mu '$tv. $t) -> mu '$tv'. $t'
          = $body parties
       in $lid:lid
    |]
build recs [$ty|+ '$tv |] [$ty|+ '$tv' |]
  | Just (Just lid) <- M.lookup (tv, tv') recs
    = return [$ex|+ $lid:lid |]
  | Just Nothing <- M.lookup (tv, tv') recs
    = return [$ex|+ INTERNALS.Contract.any ['$tv'] |]
build _ t t' =
  if t <: t'
    then return [$ex|+ INTERNALS.Contract.any [$t'] |]
    else fail $ "No coercion from " ++ show t ++ " to " ++ show t'

shadow :: [TyVar] -> [TyVar] ->
          M.Map (TyVar, TyVar) a -> M.Map (TyVar, TyVar) a
shadow tvs tvs' = M.filterWithKey
                    (\(tv, tv') _ -> tv `notElem` tvs && tv' `notElem` tvs')

absContract :: ExprT -> ExprT
absContract body =
  [$ex|+ fun (neg: string $td:string, pos: string $td:string) -> $body |]

instContract :: ExprT -> ExprT
instContract con = [$ex|+ $con (neg, pos) |]

freshLid :: Monad m => CMS.StateT Integer m Lid
freshLid = do
  n <- CMS.get
  CMS.put (n + 1)
  return (Lid ("c" ++ show n))


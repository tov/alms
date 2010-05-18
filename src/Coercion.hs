-- | Converts coercion expressions to dynamic checks.
{-# LANGUAGE
      PatternGuards,
      QuasiQuotes,
      ViewPatterns #-}
module Coercion  (
  coerceExpression,
  translate, translateDecls, TEnv, tenv0
) where

import Loc
import Meta.Quasi
import Ppr ()
import qualified Syntax
import qualified Syntax.Expr
import qualified Syntax.Notable
import qualified Syntax.Patt
import Syntax hiding (Type, Type'(..))
import Type
import TypeRel ()
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
translate :: TEnv -> Prog Renamed -> Prog Renamed
translate _ = id

-- | Location to use for constructed code
_loc :: Loc
_loc  = mkBogus "<coercion>"

-- | Translation a sequence of declarations in the context
--   of a translation environment, returning a new translation
--   environment
translateDecls :: TEnv -> [Decl Renamed] -> (TEnv, [Decl Renamed])
translateDecls tenv decls = (tenv, decls)

coerceExpression :: Monad m =>
                    Expr Renamed -> Type -> Type -> m (Expr Renamed)
coerceExpression e tfrom tto = do
  prj <- CMS.evalStateT (build True M.empty tfrom tto) 0
  return $ exApp (exApp prj (exPair (exStr neg) (exStr pos))) e
  where
  neg = "context at " ++ show (getLoc e)
  pos = "value at " ++ show (getLoc e)

build :: Monad m =>
         Bool -> M.Map (TyVarR, TyVarR) (Maybe (Lid Renamed)) ->
         Type -> Type -> CMS.StateT Integer m (Expr Renamed)
build b recs tfrom tto
  | (tvs,  TyFun qd  t1  t2)  <- vtQus Forall tfrom,
    (tvs', TyFun qd' t1' t2') <- vtQus Forall tto,
    length tvs == length tvs'
    = do
        let which = case (qConstBound qd, qConstBound qd') of
              (Qa, Qu) -> [$ex|+ INTERNALS.Contract.affunc |]
              (Qu, _ ) -> [$ex|+ INTERNALS.Contract.func[U] |]
              (_ , Qa) -> [$ex|+ INTERNALS.Contract.func[A] |]
            recs' = foldr2
                      M.insert
                      (shadow tvs tvs' recs)
                      (zip tvs tvs')
                      (repeat Nothing)
        dom <- build (not b) recs' t1' t1
        cod <- build b recs' t2 t2'
        let body = [$ex|+ $which $dom $cod |]
        return $ if null tvs
          then body
          else absContract $
               exAbsVar' (lid "f") (typeToStx tfrom) $
               foldr (\tv0 acc -> exTAbs tv0 . acc) id tvs $
               exAbsVar' (lid "x") (typeToStx t1') $
               instContract body `exApp`
               foldl (\acc tv0 -> exTApp acc (Syntax.tyVar tv0))
                     (exBVar (lid "f")) tvs `exApp`
               exBVar (lid "x")
build b recs (view -> TyQu Exists tv t) (view -> TyQu Exists tv' t') = do
  let recs' = M.insert (tv, tv') Nothing (shadow [tv] [tv'] recs)
  body <- build b recs' t t' >>! instContract
  let tv''  = freshTyVar tv (ftv (tv, tv'))
  return $
    absContract $
      [$ex|+ fun (Pack('$tv'', e) : ex '$tv. $stx:t) ->
               Pack[ex '$tv'. $stx:t']('$tv'', $body e) |]
build b recs (view -> TyMu tv t) (view -> TyMu tv' t') = do
  l    <- freshLid
  let recs' = M.insert (tv, tv') (Just l) (shadow [tv] [tv'] recs)
  body <- build b recs' t t'
  return $
    [$ex|+
      let rec $lid:l
              (parties : string * string)
                       : (mu '$tv. $stx:t) -> mu '$tv'. $stx:t'
          = $body parties
       in $lid:l
    |]
build b recs (view -> TyVar tv) (view -> TyVar tv')
  | Just (Just l) <- M.lookup (if b then (tv, tv') else (tv', tv)) recs
    = return [$ex|+ $lid:l |]
  | Just Nothing <- M.lookup (if b then (tv, tv') else (tv', tv)) recs
    = return [$ex|+ INTERNALS.Contract.any ['$tv'] |]
build _ recs t t' =
  if t <: t'
    then return [$ex|+ INTERNALS.Contract.any [$stx:t'] |]
    else fail $ "No coercion from " ++ show t ++ " to " ++ show t'
      ++ "\n" ++ show recs

shadow :: [TyVarR] -> [TyVarR] ->
          M.Map (TyVarR, TyVarR) a -> M.Map (TyVarR, TyVarR) a
shadow tvs tvs' = M.filterWithKey
                    (\(tv, tv') _ -> tv `notElem` tvs && tv' `notElem` tvs')

absContract :: Expr Renamed -> Expr Renamed
absContract body =
  [$ex|+ fun (neg: string, pos: string) -> $body |]

instContract :: Expr Renamed -> Expr Renamed
instContract con = [$ex|+ $con (neg, pos) |]

freshLid :: Monad m => CMS.StateT Integer m (Lid Renamed)
freshLid = do
  n <- CMS.get
  CMS.put (n + 1)
  return (lid ("c" ++ show n))


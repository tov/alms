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
import Ppr ()
import Quasi
import qualified Syntax
import Syntax hiding (Type(..))
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
translate :: TEnv -> Prog i -> Prog i
translate _ = id

-- | Location to use for constructed code
_loc :: Loc
_loc  = mkBogus "<coercion>"

-- | Translation a sequence of declarations in the context
--   of a translation environment, returning a new translation
--   environment
translateDecls :: TEnv -> [Decl i] -> (TEnv, [Decl i])
translateDecls tenv decls = (tenv, decls)

coerceExpression :: Monad m => Expr i -> Type -> Type -> m (Expr i)
coerceExpression e tfrom tto = do
  prj <- CMS.evalStateT (build M.empty tfrom tto) 0
  return $ exApp (exApp prj (exPair (exStr neg) (exStr pos))) e
  where
  neg = "context at " ++ show (getLoc e)
  pos = "value at " ++ show (getLoc e)

build :: Monad m =>
         M.Map (TyVar, TyVar) (Maybe Lid) -> Type -> Type ->
         CMS.StateT Integer m (Expr i)
build recs tfrom tto
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
        dom <- build recs' t1' t1
        cod <- build recs' t2 t2'
        let body = [$ex|+ $which $dom $cod |]
        return $ if null tvs
          then body
          else absContract $
               exAbsVar' (Lid "f") (typeToStx tfrom) $
               foldr (\tv0 acc -> exTAbs tv0 . acc) id tvs $
               exAbsVar' (Lid "x") (typeToStx t1') $
               instContract body `exApp`
               foldl (\acc tv0 -> exTApp acc (Syntax.TyVar tv0))
                     (exBVar (Lid "f")) tvs `exApp`
               exBVar (Lid "x")
build recs (view -> TyQu Exists tv t) (view -> TyQu Exists tv' t') = do
  let recs' = M.insert (tv, tv') Nothing (shadow [tv] [tv'] recs)
  body <- build recs' t t' >>! instContract
  let tv''  = freshTyVar tv (ftv (tv, tv'))
  return $
    absContract $
      [$ex|+ fun (Pack('$tv'', e) : ex '$tv. $stx:t) ->
               Pack[ex '$tv'. $stx:t']('$tv'', $body e) |]
build recs (view -> TyMu tv t) (view -> TyMu tv' t') = do
  lid  <- freshLid
  let recs' = M.insert (tv, tv') (Just lid) (shadow [tv] [tv'] recs)
  body <- build recs' t t'
  return $
    [$ex|+
      let rec $lid:lid
              (parties : string * string)
                       : (mu '$tv. $stx:t) -> mu '$tv'. $stx:t'
          = $body parties
       in $lid:lid
    |]
build recs (view -> TyVar tv) (view -> TyVar tv')
  | Just (Just lid) <- M.lookup (tv, tv') recs
    = return [$ex|+ $lid:lid |]
  | Just Nothing <- M.lookup (tv, tv') recs
    = return [$ex|+ INTERNALS.Contract.any ['$tv'] |]
build _ t t' =
  if t <: t'
    then return [$ex|+ INTERNALS.Contract.any [$stx:t'] |]
    else fail $ "No coercion from " ++ show t ++ " to " ++ show t'

shadow :: [TyVar] -> [TyVar] ->
          M.Map (TyVar, TyVar) a -> M.Map (TyVar, TyVar) a
shadow tvs tvs' = M.filterWithKey
                    (\(tv, tv') _ -> tv `notElem` tvs && tv' `notElem` tvs')

absContract :: Expr i -> Expr i
absContract body =
  [$ex|+ fun (neg: string, pos: string) -> $body |]

instContract :: Expr i -> Expr i
instContract con = [$ex|+ $con (neg, pos) |]

freshLid :: Monad m => CMS.StateT Integer m Lid
freshLid = do
  n <- CMS.get
  CMS.put (n + 1)
  return (Lid ("c" ++ show n))


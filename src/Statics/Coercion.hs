-- | Converts coercion expressions to dynamic checks.
module Statics.Coercion  (
  coerceExpression,
) where

import Util
import Util.MonadRef
import qualified AST
import AST.Ident
import Data.Loc
import Meta.Quasi
import Error
import Type
import Statics.Constraint

import Prelude ()
import qualified Data.Map as M

-- | Location to use for constructed code
_loc :: Loc
_loc  = mkBogus "<coercion>"

type R = AST.Renamed

-- | Coerce an expression from one type to another, if possible.
coerceExpression :: MonadConstraint tv r m ⇒
                    AST.Expr R → Type tv → Type tv → m (AST.Expr R)
coerceExpression e σfrom σto = do
  σfrom' ← subst σfrom
  σto'   ← subst σto
  prj    ← evalStateT (build mempty σfrom' σto') 0 `catchAlms` handler
  return [ex|+ $prj ($str:neg, $str:pos) $e |]
  where
  neg = "context at " ++ show (getLoc e)
  pos = "value at " ++ show (getLoc e)
  mapMsg f exn = exn { exnMessage = f (exnMessage exn) }
  handler =
    throwAlmsList .
    map (mapMsg [msg| While constructing coercion (:>): <br> $1 |]) .
    mapHead (mapMsg
      [msg|
        $1
        <p>
        Could not construct coercion
        <dl>
          <dt>from type: <dd>$σfrom
          <dt>to type:   <dd>$σto.
        </dl>
        <p>
        Hints:
        <ul>
          <li>
            Coercions may be constructed only between (possibly
            quantified) arrow types.  All other types must be
            unifiable as subtypes.
          <li>
            Coercion construction may fail if either the type of
            the expression or the requested coercion type is
            incomplete due to type inference, so it may help to
            add a non-coercing type annotation to the term
            inside the coercion, like <q>(e : τfrom :> τto)</q>.
        </ul>
      |])

type RecMap tv r = M.Map (Type tv, Type tv) (VarId R, r Bool)

build :: (MonadConstraint tv r m, MonadState Integer m) ⇒
         RecMap tv r → Type tv → Type tv → m (AST.Expr R)

build μ σfrom σto
  | Just (x, used) ← M.lookup (σfrom, σto) μ
  = do
    writeRef used True
    return [ex| $vid:x |]

build μ σfrom@(TyMu _ σfrom') σto
  = remember μ σfrom σto $ \μ' →
      build μ' (openTy 0 [σfrom] σfrom') σto

build μ σfrom σto@(TyMu _ σto')
  = remember μ σfrom σto $ \μ' →
      build μ' σfrom (openTy 0 [σto] σto')

build μ (TyQu Forall tvs1 σfrom) (TyQu Forall tvs2 σto)
  | length tvs1 == length tvs2
  , all2 (⊑) (snd <$> tvs1) (snd <$> tvs2)
  = build μ σfrom σto

build μ (TyQu Exists tvs1 σfrom) (TyQu Exists tvs2 σto)
  | tvs1 == tvs2
  = build μ σfrom σto

build μ (TyApp tc1 [σf1, qf, σf2]) (TyApp tc2 [σt1, qt, σt2])
  | tc1 == tcFun, tc2 == tcFun
  = do
    dom ← build μ σt1 σf1
    cod ← build μ σf2 σt2
    let which = contractIdent $
          if qualifier qf ⊑ qualifier qt
            then "func"
            else "affunc"
    return [ex| $qvid:which $dom $cod |]

build _ σfrom σto
  = do
    σfrom <: σto
    return [ex| $qvid:anyId |]
    where anyId = contractIdent "any"

-- | Get the identifier for a known name from the contracts library.
contractIdent ∷ String → QVarId R
contractIdent = qident . ("INTERNALS.Contract." ++)

-- | Remember a coercion to use it recursively later.
remember ∷ (MonadConstraint tv r m, MonadState Integer m) ⇒
           RecMap tv r → Type tv → Type tv →
           (RecMap tv r → m (AST.Expr R)) →
           m (AST.Expr R)
remember μ σfrom σto k = do
  c      ← freshVarId
  rused  ← newRef False
  result ← k (M.insert (σfrom, σto) (c, rused) μ)
  used   ← readRef rused
  return $ if used
    then [ex| let rec $vid:c = $result in $vid:c |]
    else result

-- | Get a fresh variable name to build a recursive coercion.
freshVarId :: MonadState Integer m ⇒ m (VarId R)
freshVarId = do
  n ← get
  put (n + 1)
  return (ident ("c" ++ show n))


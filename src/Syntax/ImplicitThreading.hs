-- | Translation of bang patterns, which introduce implicit threading.
module Syntax.ImplicitThreading (
  threadDecls, threadDecl, threadProg,
) where

import Util
import AST
import Data.Loc
import Error
import Meta.Quasi
import Syntax.Construction
import qualified Syntax.Ppr as Ppr

import Prelude ()
import Data.Generics (Data, everywhere, mkT, extT)
import qualified Data.Map as M
import qualified Data.Set as S

type R = Raw
type ThreadTrans a = MonadAlmsError m ⇒ a → m a

threadProg  ∷ ThreadTrans (Prog R)
threadDecls ∷ ThreadTrans [Decl R]
threadDecl  ∷ ThreadTrans (Decl R)

threadProg [prQ| $list:ds in $opt:me |] = do
  ds' ← mapM threadDecl ds
  me' ← mapM threadExpr me
  return [prQ| $list:ds' in $opt:me' |]

threadDecls = mapM threadDecl

threadDecl d0 = withLocation d0 $ case d0 of
  [dc| let $π = $e |]
    → do
    withLocation π $
      bassert (not (patternHasBang π)) [msg|
        Implicit threading translation does not allow ! patterns to appear
        declaration let bindings.
      |]
    e' ← threadExpr e
    return [dc| let $π = $e' |]
  [dc| let rec $list:bns |]
    → do
    bns' ← mapM threadBinding bns
    return [dc| let rec $list:bns' |]
  [dc| type $list:_ |] → return d0
  [dc| type $tid:_ = type $qtid:_ |] → return d0
  [dc| abstype $list:abstys with $list:ds end |]
    → do
      ds' ← mapM threadDecl ds
      return [dc| abstype $list:abstys with $list:ds' end |]
  [dc| module $mid:mid = $modexp |]
    → do
      modexp' ← threadModExp modexp
      return [dc| module $mid:mid = $modexp' |]
  [dc| module type $sid:_ = $_ |] → return d0
  [dc| open $modexp |]
    → do
      modexp' ← threadModExp modexp
      return [dc| open $modexp' |]
  [dc| local $list:ds1 with $list:ds2 end |]
    → do
      ds1' ← mapM threadDecl ds1
      ds2' ← mapM threadDecl ds2
      return [dc| local $list:ds1' with $list:ds2' end |]
  [dc| exception $uid:_ of $opt:_ |] → return d0
  [dc| $anti:a |] → $antifail

threadModExp ∷ ThreadTrans (ModExp R)
threadModExp modexp0 = withLocation modexp0 $ case modexp0 of
  [meQ| struct $list:ds end |]
    → do
      ds' ← mapM threadDecl ds
      return [meQ| struct $list:ds' end |]
  [meQ| $qmid:_ $list:_ |] → return modexp0
  [meQ| $modexp : $sigexp |]
    → do
      modexp' ← threadModExp modexp
      return [meQ| $modexp' : $sigexp |]
  [meQ| $anti:a |] → $antifail

threadBinding ∷ ThreadTrans (Binding R)
threadBinding bn0 = withLocation bn0 $ case bn0 of
  [bnQ| $vid:x = $e |]
    → do
    e' ← threadExpr e
    return [bnQ| $vid:x = $e' |]
  [bnQ| $antiB:a |] → $antifail

threadCaseAlt ∷ ThreadTrans (CaseAlt R)
threadCaseAlt ca0 = case ca0 of
  [caQ| $π → $e |]
    | (π', xs@(_:_)) ← patternBangRename π
    → do
    e'          ← beginTranslate xs e
    return [caQ| $π' → $e' |]
    | otherwise
    → do
    e'          ← threadExpr e
    return [caQ| $π → $e' |]
  [caQ| #$uid:c $opt:mπ → $e |]
    | Just (π', xs@(_:_)) ← patternBangRename <$> mπ
    → do
    e'          ← beginTranslate xs e
    return [caQ| #$uid:c $π' → $e' |]
    | otherwise
    → do
    e'          ← threadExpr e
    return [caQ| #$uid:c $opt:mπ → $e' |]
  [caQ| $antiC:a |] → $antifail

threadExpr ∷ ThreadTrans (Expr R)
threadExpr e = case e of
  [ex| $qvid:_ |]               → return e
  [ex| $lit:_   |]              → return e
  [ex| $qcid:c $opt:me |]
    → do
    me'         ← mapM threadExpr me
    return [ex| $qcid:c $opt:me' |]
  [ex| let $π = $e1 in $e2 |]
    | (π', xs@(_:_)) ← patternBangRename π
    → do
    e1'         ← threadExpr e1
    e2'         ← beginTranslate xs e2
    return [ex| let $π' = $e1' in $e2' |]
    | otherwise
    → do
    e1'         ← threadExpr e1
    e2'         ← threadExpr e2
    return [ex| let $π = $e1' in $e2' |]
  [ex| match $e0 with $list:cas |]
    → do
    e0'         ← threadExpr e0
    cas'        ← mapM threadCaseAlt cas
    return [ex| match $e0' with $list:cas' |]
  [ex| let rec $list:bns in $e1 |]
    → do
    bns'        ← mapM threadBinding bns
    e1'         ← threadExpr e1
    return [ex| let rec $list:bns' in $e1' |]
  [ex| let $decl:d in $e1 |]
    → do
    d'          ← threadDecl d
    e1'         ← threadExpr e1
    return [ex| let $decl:d' in $e1' |]
  [ex| ($e1, $e2) |]
    → do
    e1'         ← threadExpr e1
    e2'         ← threadExpr e2
    return [ex| ($e1', $e2') |]
  [ex| λ $π → $e2 |]
    | (π', xs@(_:_)) ← patternBangRename π
    → do
    e2'         ← beginTranslate xs e2
    return [ex| λ $π' → $e2' |]
    | otherwise
    → do
    e2'         ← threadExpr e2
    return [ex| λ $π → $e2' |]
  [ex| $e1 $e2 |]
    → do
    e1'         ← threadExpr e1
    e2'         ← threadExpr e2
    return [ex| $e1' $e2' |]
  [ex| `$uid:c $opt:me |]
    → do
    me'         ← mapM threadExpr me
    return [ex| `$uid:c $opt:me' |]
  [ex| #$uid:c $e2 |]
    → do
    e2'         ← threadExpr e2
    return [ex| #$uid:c $e2' |]
  [ex| $e1 : $annot |]
    → do
    e1'         ← threadExpr e1
    return [ex| $e1' : $annot |]
  [ex| $e1 :> $annot |]
    → do
    e1'         ← threadExpr e1
    return [ex| $e1' :> $annot |]
  [ex| $anti:_ |] → return e

-- Synthesized attributes
data Synth
  = S {
      code      ∷ !(Expr R),
      typ       ∷ ![[VarId R]],
      vars      ∷ ![VarId R]
    }
  deriving Show

beginTranslate ∷ MonadAlmsError m ⇒ [VarId R] → Expr R → m (Expr R)
beginTranslate env0 e00 = do
  let e00_env = S.fromList env0
  e00' ← loop e00_env M.empty e00
  return $
    exLet' (r1 -*- vars e00') (code e00') $
      r1 -*- ren env0
  where
  loop env funs e = withLocation e $ case e of
    [ex| λ $π → $e1 |]
      → do
      let (π', new) = patternBangRename π
          e1_env    = (env ∖ dv π) ∪ new
      e1' ← loop e1_env funs e1
      let latent    = vars e1' ∖ ren new
          body      = optExAbs latent                           $
                        exLet' (r1 -*- vars e1') (code e1')     $
                          r1 -*- ren new ++ latent
      return S {
        vars = emptySet,
        typ  = latent : typ e1',
        code = [ex| λ $π' → $body |]
      }
    --
    [ex| $e1 $e2 |]
      | Just (_, dv_π2) ← expr2patt env e2
      → do
        e1'     ← loop env funs e1
        let (latent, cod_e1_typ) = splitType (typ e1')
            e_vars       = toList (vars e1' ∪ ren dv_π2 ∪ latent)
            interference = ren dv_π2 ∩ latent
            e2'          = ren e2
        bassert (null interference) $
          [msg|
            In implicit threading syntax expansion, the
            the operand of an application expression uses the
            some imperative variables that were also captured
            by the definition of the operator:
            <dl>
              <dt>operator:  <dd>$5:e1
              <dt>operand:   <dd>$5:e2
              <dt>variables: <dd>$interference
            </dl>
          |]
        return S {
          vars  = e_vars,
          typ   = cod_e1_typ,
          code  = exLet' (r1 -*- vars e1') (code e1')           $
                  exLet' (r2 -*- ren dv_π2 ++ latent)
                         (optExApp [ex| $vid:r1 $e2' |] latent) $
                    r2 -*- e_vars
        }
      | otherwise
      → do
        e1'     ← loop env funs e1
        e2'     ← loop env funs e2
        assertCapture e2' "operand of an application expression" e2
        let (latent, cod_e1_typ) = splitType (typ e1')
            e_vars = toList (vars e1' ∪ vars e2' ∪ latent)
        return S {
          vars  = e_vars,
          typ   = cod_e1_typ,
          code  = exLet' (r1 -*- vars e1') (code e1')   $
                  exLet' (r2 -*- vars e2') (code e2')   $
                  exLet' (r -*- latent)
                         (optExApp [ex| $vid:r1 $vid:r2 |] latent) $
                    r -*- e_vars
        }
    --
    [ex| $vid:x |]
      | x ∈ env
      → return S {
          vars = [ren x],
          typ  = [],
          code = exPair (ren e) exUnit
        }
      | otherwise
      → return S {
          vars = [],
          typ  = M.findWithDefault [] x funs,
          code = e
        }
    [ex| $qvid:_ |]
      → return S {
          vars = [],
          typ  = [],
          code = e
        }
    [ex| $qcid:_ |]
      → return S {
          vars = [],
          typ  = [],
          code = e
        }
    [ex| $qcid:c1 $e2 |]
      → do
        e2' ← loop env funs e2
        assertCapture e2' "argument of a data constructor" e2
        return S {
          vars = vars e2',
          typ  = [],
          code = exLet' (r -*- vars e2') e2 $
                   [ex| $qcid:c1 $vid:r |] -*- vars e2'
        }
    [ex| let $π = $e1 in $e2 |]
      | Just (_, dv_π1) ← expr2patt env e1
      → do
        let (π', new) = patternBangRename π
            hidden    = dv_π1 ∖ (dv π ∖ new)
            e2_env    = (env ∖ hidden ∖ dv π) ∪ new
            e1'       = ren e1
        e2'     ← loop e2_env funs e2
        let e_vars    = ren dv_π1 ∪ (vars e2' ∖ ren new)
            e_vars'   = [ if v ∈ ren new then exUnit else toExpr v
                        | v ← e_vars ]
            body      =
              censorVars (ren (dv_π1 ∖ dv π))    $
              exLet (r2 -*- vars e2') (code e2') $
                r2 -*- (toExpr <$> ren new) ++ e_vars'
            π''       = renOnly (env ∖ new) π'
        return S {
          vars  = e_vars,
          typ   = typ e2',
          code  = [ex| let $π'' = $e1' in $body |]
        }
      | otherwise
      → do
        e1'     ← loop env funs e1
        case typ e1' of
          _:_
            | [pa| $vid:x |] ← π
            → do
              let e2_env  = env ∖ [x]
                  e2_funs = M.insert x (typ e1') funs
              e2'         ← loop e2_env e2_funs e2
              let e_vars  = vars e1' ∪ vars e2'
              return S {
                vars = e_vars,
                typ  = typ e2',
                code = (exLet (x -*- vars e1') (code e1') $
                        exLet' (r2 -*- vars e2') (code e2') $
                          r2 -*- e_vars)
                       <<@ _loc
              }
          _ → do
              assertCapture e1' "right-hand side of a let expression" e1
              let (π', new)     = patternBangRename π
                  e2_env        = env ∪ new
              e2'               ← loop e2_env funs e2
              let e_vars        = vars e1' ∪ (vars e2' ∖ ren new)
              return S {
                vars = e_vars,
                typ  = typ e2',
                code = (exLet (r1 -*- vars e1') (code e1')      $
                        exLet' (r2 -*- r : (vars e2' ∖ ren new))
                               (exLet' π' (toExpr r1)    $
                                exLet' (r2 -*- vars e2') (code e2') $
                                  ((r2 -*- ren new ∷ Expr Raw)
                                     -*- (vars e2' ∖ ren new)))  $
                          (r2 -*- r : e_vars))
                      <<@ _loc
              }
    [ex| $lit:_ |]
      → return S {
          vars = [],
          typ  = [],
          code = e
        }
    --
    [ex| match $e0 with $list:cas |]
      → do
        (used, changed, rhs) ←
          case expr2patt env e0 of
            Just (_, dv_π0) → return (S.fromList dv_π0, [], ren e0)
            Nothing         → do
              e0' ← loop env funs e0
              assertCapture e0' "expression in match" e0
              return (emptySet, vars e0', code e0')
        let decompose [caQ|@=loc $πi → $ei |]
                    = let (πi', newi) = patternBangRename πi
                       in (dv πi, newi ∖ used, Left πi', ei, loc)
            decompose [caQ|@=loc #$uid:c → $ei |]
                    = ([], [], Right (c, Nothing), ei, loc)
            decompose [caQ|@=loc #$uid:c $πi → $ei |]
                    = let (πi', newi) = patternBangRename πi
                       in (dv πi, newi ∖ used, Right (c, Just πi'), ei, loc)
            decompose [caQ|@=loc $antiC:a |] = $antierror
        let (dv_πs, news, eπs', es, locs)
                    = unzip5 (decompose <$> cas)
            hides   = ren ((used ∖) <$> dv_πs)
            ei_envs = zipWith (\dv_πi newi → (env ∖ dv_πi) ∪ used ∪ newi)
                              dv_πs news
        synths  ← zipWithM (loop <-> funs) ei_envs es
        let e_vars  = foldl' (∪) (changed ∪ ren used)
                                 (zipWith (∖) (vars <$> synths) (ren news))
            e_typ   = foldl' joinType [] (typ <$> synths)
            coerces = (`coerceType` e_typ) <$> typ <$> synths
            cas'    = [ let body = censorVars (toList hidei)          $
                                   exLet' (r -*- vars ei') (code ei') $
                                     coercei -*- e_vars
                         in case renOnly used eπi' of
                              Left πi'
                                → [caQ|@=loc $πi' → $body |]
                              Right (c, mπi')
                                → [caQ|@=loc #$uid:c $opt:mπi' → $body |]
                      | eπi'    ← eπs'
                      | hidei   ← hides
                      | ei'     ← synths
                      | coercei ← coerces
                      | loc     ← locs]
        return S {
          vars = e_vars,
          typ  = e_typ,
          code = exLet' (r -*- changed) rhs $
                 [ex| match $vid:r with $list:cas' |]
        }
    --
    [ex| let rec $list:bns in $e2 |]
      → do
        -- We infer the types of recursive functions by iterating to
        -- a fixpoint.  Does this terminate?  I believe it's monotone
        -- and in a finite domain, so it should.
        let bloop previous = do
              let env'  = env ∖ (fst <$> previous)
                  funs' = foldr (uncurry M.insert) funs previous
              (fτs, bns') ← unzip `liftM` mapM (binding env' funs') bns
              if (previous == fτs)
                then return (env', funs', bns')
                else bloop fτs
        (e2_env, e2_funs, bns') ← bloop []
        e2'                     ← loop e2_env e2_funs e2
        let e2_code             = code e2'
        return S {
          vars = vars e2',
          typ  = typ e2',
          code = [ex| let rec $list:bns' in $e2_code |]
        }
    [ex| let $decl:d in $e2 |]
      → do
        d'              ← threadDecl d
        -- Note: decl bindings do not shadow bang variables
        e2'             ← loop env funs e2
        let e2_code     = code e2'
        return S {
          vars = vars e2',
          typ  = typ e2',
          code = [ex| let $decl:d' in $e2_code |]
        }
    [ex| ($e1, $e2) |]
      → do
        e1' ← loop env funs e1
        e2' ← loop env funs e2
        assertCapture e1' "tuple component" e1
        assertCapture e2' "tuple component" e2
        let e_vars = vars e1' ∪ vars e2'
        return S {
          vars  = e_vars,
          typ   = [],
          code  = exLet' (r1 -*- vars e1') (code e1') $
                  exLet' (r2 -*- vars e2') (code e2') $
                    [ex| ($vid:r1, $vid:r2) |] -*- e_vars
        }
    [ex| `$uid:_ |]
      → return S {
          vars = [],
          typ  = [],
          code = e
        }
    [ex| `$uid:c1 $e2 |]
      → do
        e2' ← loop env funs e2
        assertCapture e2' "argument of a variant constructor" e2
        return S {
          vars = vars e2',
          typ  = [],
          code = exLet' (r -*- vars e2') e2 $
                   [ex| `$uid:c1 $vid:r |] -*- vars e2'
        }
    [ex| #$uid:c1 $e2 |]
      → do
        e2' ← loop env funs e2
        assertCapture e2' "argument of a variant embedding" e2
        return S {
          vars = vars e2',
          typ  = [],
          code = exLet' (r -*- vars e2') e2 $
                   [ex| #$uid:c1 $vid:r |] -*- vars e2'
        }
    [ex| $e1 : $annot |]
      → do
        e1' ← loop env funs e1
        return S {
          vars = vars e1',
          typ  = typ e1',
          code = exLet' (r -*- vars e1') e1 $
                   [ex| $vid:r : $annot |] -*- vars e1'
        }
    [ex| $e1 :> $annot |]
      → do
        e1' ← loop env funs e1
        return S {
          vars = vars e1',
          typ  = typ e1',
          code = exLet' (r -*- vars e1') e1 $
                   [ex| $vid:r :> $annot |] -*- vars e1'
        }
    [ex| $anti:a |]
      → $antifail
  --
  binding env funs bn = withLocation bn $ case bn of
    [bnQ| $vid:f = $e |] → do
      let env_e = env ∖ [f]
      e'        ← loop env_e funs e
      bassert (null (vars e')) $
        [msg|
          In implicit threading syntax expansion, imperative variables
          may not be used on the right-hand side of a let rec binding
          unless they occur in the body of a function.
          <dl>
            <dt>In binding:      <dd> $f
            <dt>Used variables:  <dd> $1
          </dl>
        |]
        (vars e')
      let e_code        = code e'
      return ((f, typ e'), [bnQ| $vid:f = $e_code |])
    [bnQ| $antiB:a |]    → $antifail


-- Find the least-upper bound of two variable/effect types.
joinType ∷ [[VarId R]] → [[VarId R]] → [[VarId R]]
joinType (vs1:rest1) (vs2:rest2) = (vs1 ∪ vs2) : joinType rest1 rest2
joinType []          τ2          = τ2
joinType τ1          []          = τ1

-- | Coerce a value whose variable/effect type is the first argument
--   to have the effect of the second. Assumes that the second subsumes
--   the first.  Assumes that the value is named @r@.
coerceType ∷ [[VarId R]] → [[VarId R]] → Expr R
coerceType _            []           = toExpr r
coerceType reste        restg
  | reste == restg                   = toExpr r
coerceType []           (gots:restg) =
  exAbsVar' r1 $
    optExAbs gots $
      exLetVar' r (exApp (toExpr r) (toExpr r1)) $
        coerceType [] restg -*- gots
coerceType (exps:reste) (gots:restg) =
  exAbsVar' r1 $
    optExAbs gots $
      exLet' (r -*- exps)
             (optExApp (exApp (toExpr r) (toExpr r1)) exps) $
        coerceType reste restg -*- gots

-- | Shadow some variables with @()@.
censorVars        ∷ [VarId R] → Expr R → Expr R
censorVars []     = id
censorVars (v:vs) = exLet' (v -*- vs) (exUnit -*- exUnit <$ vs)

-- Given an expression and a list, apply the expression to the
-- tuple of the list only if the list is non-empty.
optExApp  ∷ (Tag i, ToExpr a i) ⇒ Expr i → [a] → Expr i
optExApp e0 []          = e0
optExApp e0 (e1:es)     = exApp e0 (e1 -*- es)

-- Given an expression and a list, abstract to a tuple pattern
-- of the list only if the list is non-empty.
optExAbs  ∷ (Tag i, ToPatt a i) ⇒ [a] → Expr i → Expr i
optExAbs []      e0    = e0
optExAbs (π1:πs) e0    = exAbs' (π1 -*- πs) e0

-- Split a type into the latent effect and the codomain
splitType ∷ [[a]] → ([a], [[a]])
splitType []     = ([], [])
splitType (v:vs) = (v, vs)

-- | Given a pattern, rename any !-ed variables, remove the ! itself,
--   and return the list of renamed variables.
patternBangRename ∷ Patt R → (Patt R, [VarId R])
patternBangRename = runWriter . loop False
  where
  loop doIt π0 = case π0 of
    [pa| $vid:x  |]
      | doIt                       → do
        tell [x]
        let x' = ren x
        return [pa| $vid:x' |]
      | otherwise                 → return π0
    [pa| _ |]                     → return π0
    [pa| $qcid:c $opt:mπ |]       → do
      mπ' ← mapM (loop doIt) mπ
      return [pa| $qcid:c $opt:mπ' |]
    [pa| ($π1, $π2) |]            → do
      π1' ← loop doIt π1
      π2' ← loop doIt π2
      return [pa| ($π1', $π2') |]
    [pa| $lit:_ |]                → return π0
    [pa| $π as $vid:x |]          → do
      π' ← loop doIt π
      return [pa| $π' as $vid:x |]
    [pa| `$uid:c $opt:mπ |]       → do
      mπ' ← mapM (loop doIt) mπ
      return [pa| `$uid:c $opt:mπ' |]
    [pa| $π : $annot |]           → do
      π' ← loop doIt π
      return [pa| $π' : $annot |]
    [pa| ! $π |]                  → loop True π
    [pa| $anti:a |]               → $antifail

patternHasBang ∷ Patt i → Bool
patternHasBang π0 = case π0 of
  [pa| $vid:_  |]               → False
  [pa| _ |]                     → False
  [pa| $qcid:_ $opt:mπ |]       → maybe False patternHasBang mπ
  [pa| ($π1, $π2) |]            → patternHasBang π1 || patternHasBang π2
  [pa| $lit:_ |]                → False
  [pa| $π as $vid:_ |]          → patternHasBang π
  [pa| `$uid:_ $opt:mπ |]       → maybe False patternHasBang mπ
  [pa| $π : $_ |]               → patternHasBang π
  [pa| ! $_ |]                  → True
  [pa| $anti:a |]               → $antierror

ren :: Data a => a → a
ren = everywhere (mkT eachRaw `extT` eachRen) where
  eachRaw ∷ VarId Raw     → VarId Raw
  eachRen ∷ VarId Renamed → VarId Renamed
  eachRaw = each; eachRen = each
  each    ∷ Tag i ⇒ VarId i → VarId i
  each (VarId (LidAnti a)) = VarId (LidAnti a)
  each (VarId (Lid i s))   = VarId (Lid i (s ++ "!"))

renOnly :: ∀ a i. (Data a, Tag i) ⇒ S.Set (VarId i) → a → a
renOnly set = everywhere (mkT each) where
  each    ∷ VarId i → VarId i
  each vid | vid `S.member` set = ren vid
           | otherwise          = vid

{-
---- The first order, one variable case:

  (x is the variable name, y is the fresh state name)

  fun !(x:t) -> e     ===  fun y:t -> [[ e ]]
  let !x = e1 in e2   ===   let y = e1 in [[ e ]]

  [[ e1 x ]]  = let (r, y) = [[ e1 ]] in
                  r y
  [[ e1 e2 ]] = let (r1, y) = [[ e1 ]] in
                let (r2, y) = [[ e2 ]] in
                  (r1 r2, y)
  [[ x ]]     = (y, ())
  [[ v ]]     = (v, y)
  [[ match e with
     | p1 -> e1
     | ...
     | pk -> ek ]]
              = let (r, y) = [[ e ]] in
                match r with
                | p1 -> [[ e1 ]]
                | ...
                | pk -> [[ ek ]]
  [[ c e ]]   = let (r, y) = [[ e ]] in
                  (c r, y)

-- The first order pattern case (2):

  (p! is a renaming of p)

  fun !(p:t) -> e     ===   fun p!:t -> 
                            let (r1, e.vars) = e.code
                             in (r1, p!)
                            where e.env = dv p in
  let !p = e1 in e2   ===   let p! = e1 in
                            let (r1, e.vars) = e.code
                             in (r1, p!)
                            where e.env = dv p in

  e ::= e1 p2   | dv p2 `subseteq` dv e.env && dv p2 != empty

    e1.env  = e.env
    e.vars  = e1.vars `union` dv p2!
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, p2!)     = r1 p2! in
                (r2, e.vars)

  e ::= e1 e2

    e1.env  = e2.env = e.env
    e.vars  = e1.vars `union` e2.vars
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, e2.vars) = e2.code in
                (r1 r2, e.vars)

  e ::= x       | x `member` dv p

    e.vars  = x!
    e.code  = (x!, ())

  e ::= v

    e.vars  = fv v `intersect` env
    e.code  = let e.vars = e.vars! in
              (v, [ () | _ <- e.vars ])

  e ::= match p0 with
        | p1 -> e1
        | ...
        | pk -> ek
                | dv p0 `subseteq` dv e.env && dv p0 != empty

    if p1 is a bang pattern
      then e1.env  = e.env `union` dv p1
      else e1.env  = e.env - (dv p1 - dv p0)
    ...
    if pk is a bang pattern
      then ek.env  = e.env `union` dv pk
      else ek.env  = e.env - (dv pk - dv p0)

    e.vars  = e.env `intersection` (e1.vars `union` ... `union` ek.vars)
    e.code  = match p0! with
              | p1[p0!/p0] -> let (p0 - p1)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)
              | ...
        (if pk is not a bang pattern then)
              | pk[p0!/p0] -> let (p0 - pk)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)
        (else)
              | pk!        -> let (p0 - pk)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)

  e ::= match e0 with
        | p1 -> e1
        | ...
        | pk -> ek

    e0.env  = e.env
    e1.env  = e.env - dv p1
    ...
    ek.env  = e.env - dv pk

    e.vars  = e.env `intersection`
                (e0.vars `union` e1.vars `union` ... `union` ek.vars)
    e.code  = let (r1, e0.vars) = e0.code in
              match r1 with
              | p1 -> let (r2, e1.vars) = e1.code in (r2, e.vars)
              | ...
              | pk -> let (r2, ek.vars) = ek.code in (r2, e.vars)

  e ::= let rec f1 = v1
            and ...
            and fk = vk
         in e1

    captured = { x `in` (fv v1 `union` ... `union` fv vk)
               | x! `in` e.env }

    e1.env  = e.env - { f1, ..., fk }
    e.vars  = e1.vars `union` captured!
    e.code  = let captured  = captured! in
              let captured! = ((), ..., ()) in
              let rec f1 = v1
                  and ...
                  and fk = vk
               in let (r1, e1.vars) = e1.code
                   in (r1, e.vars)

  e ::= let !p1 = e1 in e2

    e1.env  = e.env
    e2.env  = e.env `union` dv p1
    e.vars  = e1.vars `union` (e2.vars `intersection` e.env)
    e.code  = let (p1!, e1.vars) = e1.code in
              let (r2,  e2.vars) = e2.code in
                ((r2, p1!), e.vars)
    [assuming no shadowing]

-- The pattern and function case (3):

  Types:
    τ ∷= 1 → τ / [VarId]
       | 1

  Inherited attributes:
    - env  ∷ S.Set VarId
    - funs ∷ S.Map VarId τ      -- τ is renamed

  Synthesized attributes:
    - vars  ∷ [VarId]           -- renamed
    - type  ∷ τ                 -- renamed
    - code  ∷ Expr

  Notation
    • e! is e renamed
    • [xs/ys]e is the substitution of xs for ys in e
    • [!xs]e = [!xs/xs]e
    • {vs} means include this only if vs is non-empty

  π → e1             ==>   [!e1.env]π →
                             let (r1, e1.vars) = e1.code
                              in (r1, !e1.env)
                           where e1.env  = bangvars(π)
                                 e1.funs = ∅

  let π = e1 in e2   ==>   let [!e.env]π = e1 in
                            let (r1, e2.vars) = e2.code
                             in (r1, !e2.env)
                            where e2.env  = bangvars π
                                  e2.funs = ∅

  e ::= λ π → e1

    new    = bangvars(π)
    latent = e1.vars \ !new

    e1.env = (e.env \ dv π) ∪ new
    e.vars = ∅
    e.type = 1 → e1.type / latent

    e.code = λ [!new]π {latent} →
               let (r, e1.vars) = e1.code in
                 (r, {!new}, {latent})

  e ::= e1 π2

    [ dv π2 nonempty ⊆ e.env ]

    latent = latent(e1.type)

      [ !(dv π2) ∩ latent ≠ ∅ ] ERROR!

    e.vars = e1.vars ∪ !(dv π2) ∪ latent
    e.type = cod(e1.type)
    e.code = let (r1, e1.vars)           = e1.code in
             let (r, !(dv π2), {latent}) = r1 !π2 {latent} in
              (r, e.vars)

  e ::= e1 e2

    [ e2.type ≠ 1 ]

    ERROR!

    latent = latent(e1.type)

    e.vars = e1.vars ∪ e2.vars ∪ latent
    e.type = cod(e1.type)
    e.code = let (r1, e1.vars)  = e1.code in
             let (r2, e2.vars)  = e2.code in
             let (r,  {latent}) = r1 r2 {latent} in
               (r, e.vars)

  e ::= x

    [ x ∈ e.env ]

    e.vars = !x
    e.type = 1
    e.code = (!x, ())

    [ otherwise ]

    e.vars = ∅
    e.type = e.funs(x) || 1
    e.code = x

  e ::= c1 e2

    [ e2.type ≠ 1 ]

    ERROR!

    [ otherwise ]

    e.vars  = e2.vars
    e.type  = 1
    e.code  = let (r, e2.vars) = e2 in
                (c1 r, e.vars)

  e ::= let π = π1 in e2

    [ dv π1 nonempty ⊆ e.env ]

    new    = bangvars(π)
    hidden = dv π1 \ (dv π \ new)

    e2.env = (e.env \ hidden \ dv π) ∪ new
    e.vars = !(dv π1) ∪ (e2.vars \ !new)
    e.type = e2.type
    e.code = let [!new][!π1]π    = !π1 in
             let !(dv π1 \ dv π) = () ... () in
             let (r2, e2.vars)   = e2.code in
               ((r2, !new), [()/!new]e.vars)

  e ::= let x = e1 in e2

    [ e1.type ≠ 1 ]

    e2.env  = e.env \ x
    e2.funs = e.funs[x ↦ e1.type]
    e.vars  = e1.vars ∪ e2.vars
    e.type  = e2.type
    e.code  = let (x, e1.vars)  = e1 in
              let (r2, e2.vars) = e2 in
                (r2, e.vars)

  e ::= let π = e1 in e2

    [ e1.type ≠ 1 ]

    ERROR!

    [ otherwise ]

    new    = bangvars(π)

    e2.env = e.env ∪ new
    e.vars = e1.vars ∪ (e2.vars \ !new)
    e.type = e2.type

    e.code = let (r1, e1.vars) = e1.code in
             let ((r2, rnew), e2.vars \ !new) =
                 let [!new]π       = r1 in
                 let (r2, e2.vars) = e2.code in
                   ((r2, !new), e2.vars \ !new) in
               (r2, rnew, e.vars)

  e ::= match e0 with
        | π1 → e1
        ⋮
        | πk → ek

  {
    [ e0 = π0 ⋀ dv π0 nonempty ⊆ e.env ]

      used    = dv π0
      changed = ∅
      rhs     = !π0

    [ e0.type ≠ 1 ]

      ERROR

    [ otherwise ]

      used    = ∅
      changed = e0.vars
      rhs     = e0.code
  }

    newᵢ   = bangvars(πᵢ) \ used
    hideᵢ  = !(used \ dv πᵢ)
    eᵢ.env = (e.env \ dv πᵢ) ∪ used ∪ newᵢ

    e.vars = !used ∪ changed ∪ (e1.vars \ !new1) ∪ ... ∪ (ek.vars \ !newk)
    e.type = e1.type ⊔ ... ⊔ ek.type
    coerceᵢ= eᵢ.type ⇝ e.type

    e.code = let (r, changed) = rhs in
               match r with
               | [!used][!new]π1 →
                   let hide1        = () ... () in
                   let (r, e1.vars) = e1.code in
                     (coerce1 r, e.vars)
               ⋮
               | [!used][!new]πk →
                   let hidek        = () ... () in
                   let (r, ek.vars) = ek.code in
                     (coercek r, e.vars)

-}

r, r1, r2 :: VarId R
r       = ident "r.!"
r1      = ident "r1.!"
r2      = ident "r2.!"

-- | Transform an expression into a pattern, if possible, using only
--   the specified variables, and return the set of variables used.
expr2patt ∷ S.Set (VarId R) → Expr R → Maybe (Patt R, [VarId R])
expr2patt vs0 e0 =
  second (reverse . snd) <$> runStateT (loop e0) (vs0, [])
  where
  loop e = case e of
    [ex| $vid:x |]                      → do
      (possible, seen) ← get
      if x `S.member` possible
        then do
          put (S.delete x possible, x:seen)
          return [pa| $vid:x |]
        else mzero
    [ex| $lit:lit |]                    → return [pa| $lit:lit |]
    [ex| $qcid:c $opt:me |]             → do
      mπ ← mapM loop me
      return [pa| $qcid:c $opt:mπ |]
    [ex| ($e1, $e2) |]                  → do
      π1 ← loop e1
      π2 ← loop e2
      return [pa| ($π1, $π2) |]
    [ex| `$uid:c $opt:me |]             → do
      mπ ← mapM loop me
      return [pa| `$uid:c $opt:mπ |]
    [ex| $e1 : $annot |]                → do
      π ← loop e1
      return [pa| $π : $annot |]
    [ex| $qvid:_ |]                     → mzero
    [ex| let $_ = $_ in $_ |]           → mzero
    [ex| match $_ with $list:_ |]       → mzero
    [ex| let rec $list:_ in $_ |]       → mzero
    [ex| let $decl:_ in $_ |]           → mzero
    [ex| λ $_ → $_ |]                   → mzero
    [ex| $_ $_ |]                       → mzero
    [ex| #$uid:_ $_ |]                  → mzero
    [ex| $anti:_ |]                     → mzero
    [ex| $_ :> $_ |]                    → mzero

-- | Transform a pattern to an expression.
patt2expr :: Patt R -> Expr R
patt2expr π0 = case π0 of
  [pa| $vid:x |]                → [ex| $vid:x |]
  [pa| _ |]                     → [ex| () |]
  [pa| $qcid:x $opt:mπ |]       → [ex| $qcid:x $opt:me |]
                                  where me = patt2expr <$> mπ
  [pa| ($π1, $π2) |]            → [ex| ($e1, $e2) |]
                                  where e1 = patt2expr π1
                                        e2 = patt2expr π2
  [pa| $lit:lit |]              → [ex| $lit:lit |]
  [pa| $π as $vid:_ |]          → patt2expr π
  [pa| `$uid:c $opt:mπ |]       → [ex| `$uid:c $opt:me |]
                                  where me = patt2expr <$> mπ
  [pa| $π : $annot |]           → [ex| $e : $annot |]
                                  where e = patt2expr π
  [pa| ! $π |]                  → patt2expr π
  [pa| $anti:a |]               → $antierror

exUnit :: Expr R
exUnit  = [ex|! () |]

paUnit :: Patt R
paUnit  = [pa|! () |]

---
--- Producing errors
---

-- | Indicate a bug in the bang translator.
bangBug         ∷ MonadAlmsError m ⇒ String → String → m a
bangBug         = throwAlms <$$> almsBug ParserPhase

-- | Indicate a bug in the bang translator, with no Alms error monad.
bangBugError    ∷ String → String → a
bangBugError    = throw <$$> almsBug ParserPhase

-- | Indicate a bang translation error.
bangError       ∷ (MonadAlmsError m, Bogus a) ⇒ Message V → m a
bangError msg0  = do
  reportAlms (AlmsError ParserPhase bogus msg0)
  return bogus

-- | Indicate a bang error.
bangError_      ∷ MonadAlmsError m ⇒ Message V → m ()
bangError_      = bangError

-- | Indicate a bang error from which we cannot recover.
bangError'      ∷ MonadAlmsError m ⇒ Message V → m a
bangError'      = throwAlms <$> AlmsError ParserPhase bogus

-- | Assert some condition, indicating a bang translation error if
--   it doesn't hold.
bassert         ∷ MonadAlmsError m ⇒ Bool → Message V → m ()
bassert True _  = return ()
bassert False m = bangError m

-- | Assert that the type of the given synthesized attribute is trivial,
--   indicating that the term it belongs to hasn't captured any bang
--   vars.  Also takes a description of the role of the term and the
--   term itself.
assertCapture   ∷ (MonadAlmsError m, Ppr.Ppr a, Ppr.Ppr b) ⇒ 
                  Synth → a → b → m ()
assertCapture e' =
  bassert (null (typ e')) <$$>
    [msg|
      In implicit threading syntax expansion, the $2 cannot be a
      function that captures some imperative variables.
      <dl>
        <dt>culprit:    <dd>$5:3
        <dt>captured:   <dd>$1
      </dl>
    |]
    (fromOpt [] (typ e'))


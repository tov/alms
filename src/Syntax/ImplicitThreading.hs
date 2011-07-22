-- | Translation of bang patterns, which introduce implicit threading.
module Syntax.ImplicitThreading (
  threadDecl, threadProg,
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

threadProg ∷ ThreadTrans (Prog R)
threadDecl ∷ ThreadTrans (Decl R)

threadProg [prQ| $list:ds in $opt:me |] = do
  ds' ← mapM threadDecl ds
  me' ← mapM threadExpr me
  return [prQ| $list:ds' in $opt:me' |]

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
threadExpr e0 = case e0 of
  [ex| $qvid:_ |]               → return e0
  [ex| $lit:_   |]              → return e0
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
  [ex| let rec $list:bns in $e |]
    → do
    bns'        ← mapM threadBinding bns
    e'          ← threadExpr e
    return [ex| let rec $list:bns' in $e' |]
  [ex| let $decl:d in $e |]
    → do
    d'          ← threadDecl d
    e'          ← threadExpr e
    return [ex| let $decl:d' in $e' |]
  [ex| ($e1, $e2) |]
    → do
    e1'         ← threadExpr e1
    e2'         ← threadExpr e2
    return [ex| ($e1', $e2') |]
  [ex| λ $π → $e |]
    | (π', xs@(_:_)) ← patternBangRename π
    → do
    e'          ← beginTranslate xs e
    return [ex| λ $π' → $e' |]
    | otherwise
    → do
    e'          ← threadExpr e
    return [ex| λ $π → $e' |]
  [ex| $e1 $e2 |]
    → do
    e1'         ← threadExpr e1
    e2'         ← threadExpr e2
    return [ex| $e1' $e2' |]
  [ex| `$uid:c $opt:me |]
    → do
    me'         ← mapM threadExpr me
    return [ex| `$uid:c $opt:me' |]
  [ex| #$uid:c $e |]
    → do
    e'          ← threadExpr e
    return [ex| #$uid:c $e' |]
  [ex| $e : $annot |]
    → do
    e'          ← threadExpr e
    return [ex| $e' : $annot |]
  [ex| $e :> $annot |]
    → do
    e'          ← threadExpr e
    return [ex| $e' :> $annot |]
  [ex| $anti:_ |] → return e0

-- Synthesized attributes
data Synth
  = S {
      code      ∷ !(Expr R),
      typ       ∷ ![[VarId R]],
      vars      ∷ ![VarId R]
    }

beginTranslate ∷ MonadAlmsError m ⇒ [VarId R] → Expr R → m (Expr R)
beginTranslate env0 e0 = do
  let e0_env = S.fromList env0
  e0' ← loop e0_env M.empty e0
  return $
    exLet' (r1 -*- vars e0') (code e0') $
      r1 -*- ren env0
  where
  loop env funs e = withLocation e $ case e of
    [ex| λ $π → $e1 |]
      → do
      let (π', new) = patternBangRename π
          e1_env    = (env ∖ dv π) ∪ new
      e1' ← loop e1_env funs e1
      let latent    = vars e1' ∖ ren new
          body      = exLet' (r1 -*- vars e1') (code e1') $
                        r1 -*- ren new ++ latent
      return S {
          vars = emptySet,
          typ  = latent : typ e1',
          code = case latent of
                   []   → [ex| λ $π' → $body |]
                   v:vs → [ex| λ $π' $vvs → $body |]
                          where vvs = v -*- vs
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
    [ex| match $_ with $list:_ |]
      → error "XXX undefined TODO"
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

-- | Shadow some variables with @()@.
censorVars        ∷ [VarId R] → Expr R → Expr R
censorVars []     = id
censorVars (v:vs) = exLet' (v -*- vs) (exUnit -*- exUnit <$ vs)

-- Given an expression and a list, apply the expression to the
-- tuple of the list only if the list is non-empty.
optExApp  ∷ (Tag i, ToExpr a i) ⇒ Expr i → [a] → Expr i
optExApp e0 []          = e0
optExApp e0 (e1:es)     = exApp e0 (e1 -*- es)

-- Split a type into the latent effect and the codomain
splitType ∷ [[a]] → ([a], [[a]])
splitType []     = ([], [])
splitType (v:vs) = (v, vs)

-- | Given a pattern, rename any !-ed variables, remove the ! itself,
--   and return the list of renamed variables.
patternBangRename ∷ Patt R → (Patt R, [VarId R])
patternBangRename = runWriter . loop False
  where
  loop ren π0 = case π0 of
    [pa| $vid:x  |]
      | ren                       → do
        let x' = ident (idName x ++ "!")
        tell [x]
        return [pa| $vid:x' |]
      | otherwise                 → return π0
    [pa| _ |]                     → return π0
    [pa| $qcid:c $opt:mπ |]       → do
      mπ' ← mapM (loop ren) mπ
      return [pa| $qcid:c $opt:mπ' |]
    [pa| ($π1, $π2) |]            → do
      π1' ← loop ren π1
      π2' ← loop ren π2
      return [pa| ($π1', $π2') |]
    [pa| $lit:_ |]                → return π0
    [pa| $π as $vid:x |]          → do
      π' ← loop ren π
      return [pa| $π' as $vid:x |]
    [pa| `$uid:c $opt:mπ |]       → do
      mπ' ← mapM (loop ren) mπ
      return [pa| `$uid:c $opt:mπ' |]
    [pa| $π : $annot |]           → do
      π' ← loop ren π
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

  e ::= match π0 with
        | π1 → e1
        ⋮
        | πk → ek

    [ dv π0 nonempty ⊆ e.env ]

    newᵢ   = bangvars(πᵢ)
    hideᵢ  = dv πᵢ \ (dv π0 \ newᵢ)

    eᵢ.env = (e.env \ hideᵢ) ∪ newᵢ
    e.vars = dv π0 ∪ (e1.vars \ new1) ∪ ... ∪ (ek.vars \ newk)
    e.type = e1.type ⊔ ... ⊔ ek.type    || ERROR!
    e.code = match π0 with
             | π1 → let dv π0 \ dv π1 = () ... () in
                    let (r, e1.vars) = e1.code in
                      (r, e.vars)
             ⋮
             | πk → let dv π0 \ dv πk = () ... () in
                    let (r, ek.vars) = ek.code in
                      (r, e.vars)

  e ::= match e0 with
        | π1 → e1
        ⋮
        | πk → ek

    [ e0.type ≠ 1 ]

    ERROR

    [ otherwise ]

    newᵢ   = bangvars(πᵢ)

    eᵢ.env = e.env ∪ newᵢ
    e.vars = e0.vars ∪ (e1.vars \ new1) ∪ ... ∪ (ek.vars \ newk)
    e.type = e1.type ⊔ ... ⊔ ek.type    || ERROR!
    e.code = let (r0, e0.vars) = e1 in
             match r0 with
             | π1 → let (r, e1.vars) = e1.code in
                      (r, e.vars)
             ⋮
             | πk → let (r, ek.vars) = ek.code in
                      (r, e.vars)

-}

{-
transform :: Tag i => S.Set (Lid i) -> Expr i -> ([Lid i], Expr i)
transform env = loop where
  capture e1
    | vars <- [ v | J [] v <- M.keys (fv e1),
                    v `S.member` env ],
      code <- translate paVar (exBVar . ren) vars .
              kill (ren vars)
        = Just (ren vars, code)
    | otherwise
        = Nothing

  unop kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              exLet' (paVar r1 -:: e1_vars) e1_code $
                (kont (exBVar r1) +:: vars)
      = (vars, code)
  unop kont ([],      e1_code)
      = ([], kont e1_code +:: [])
  unop kont (e1_vars, e1_code)
    | vars <- e1_vars,
      code <- exLet' (paPair (paVar r1) (paVar r2)) e1_code $
                exPair (kont (exBVar r1)) (exBVar r2)
      = (vars, code)

  binder kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              kont $
              exLet' (paVar r1 -:: e1_vars) e1_code $
              (exBVar r1 +:: vars)
      = (vars, code)
    | vars <- e1_vars,
      code <- kont e1_code
      = (vars, code)

  binop kont e1 e2 =
    case (loop e1, loop e2) of
      (([],      e1_code), ([],      e2_code))
          -> ([], kont e1_code e2_code +:: [])
      (([],      e1_code), (e2_vars, e2_code))
        | syntacticValue e1_code,
          vars <- e2_vars,
          code <- exLet' (paVar r2 -:: e2_vars) e2_code $
                    kont e1_code (exBVar r2) +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), ([],      e2_code))
        | syntacticValue e2_code,
          vars <- e1_vars,
          code <- exLet' (paVar r1 -:: e1_vars) e1_code $
                  kont (exBVar r1) e2_code +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), (e2_vars, e2_code))
        | vars <- e1_vars `L.union` e2_vars,
          code <- exLet' (paVar r1 -:: e1_vars) e1_code $
                  exLet' (paVar r2 -:: e2_vars) e2_code $
                    kont (exBVar r1) (exBVar r2) +:: vars
          -> (vars, code)

  shadow vs e = transform (env `S.difference` vs) e

  loop e  = let (vars, e') = loop' e in (vars, e' <<@ e)

  loop' e = case view e of
    ExId (J [] (Var x))
      | x `S.member` env,
        vars <- [ren x]
        -> (vars, ren (exBVar x) +:+ [exUnit])

    ExCase e0 bs
      | Just p0 <- expr2patt env S.empty e0,
        not (dv p0 `disjoint` env),
        e0_vars <- toList (dv (ren p0)),
        e0_code <- ren e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  ->
                (renOnly (dv p0) pj,
                 shadow (dv pj `S.difference` dv p0) ej)
              Just pj' ->
                (ren pj',
                 transform (env `S.union` dv pj) ej)
          | N _ (CaClause pj ej) <- bs ],
        vars <- [ v | v <- foldl L.union e0_vars (map (fst . snd) bs'),
                      v `S.member` ren env ],
        code <- exCase e0_code $
                  [ caClause pj (kill (dv (ren p0) `S.difference` dv pj) $
                         exLet' (paVar r1 -:: ej_vars) ej_code $
                           (exBVar r1 +:: vars))
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

      | (e0_vars, e0_code) <- loop e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  -> (pj, shadow (dv pj) ej)
              Just pj' -> exAddSigma
                            (length bs == 1)
                            (\vars patt expr -> (patt, (vars, expr)))
                            env pj' ej
          | N _ (CaClause pj ej) <- bs ],
        vars <- foldl L.union e0_vars (map (fst . snd) bs'),
        code <- exLet' (paVar r1 -:: e0_vars) e0_code $
                exCase (exBVar r1) $
                  [ caClause pj
                             (exLet' (paVar r2 -:: ej_vars) ej_code $
                                exBVar r2 +:: vars)
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

    ExLetRec bs e1
        -> binder (exLetRec bs)
             (shadow (S.fromList (map (bnvar . dataOf) bs)) e1)

    ExLetDecl ds e1
        -> binder (exLetDecl ds) (loop e1)

    ExPair e1 e2
        -> binop exPair e1 e2

    ExApp e1 e2
      | Just p2 <- expr2patt env S.empty e2,
        not (dv p2 `disjoint` env),
        (e1_vars, e1_code) <- loop e1,
        vars <- e1_vars `L.union` toList (dv (ren p2)),
        (v1, f1) <- if null e1_vars
                      then (e1_code, id)
                      else (exBVar r1,
                            exLet' (paVar r1 -:: e1_vars) e1_code),
        code <- f1 $
                exLet' (paPair (paVar r2) (flatpatt (ren p2)))
                       (exApp v1 (ren e2)) $
                exBVar r2 +:: vars
        -> (vars, code)

      | otherwise
        -> binop exApp e1 e2

    ExTApp e1 t2
        -> unop (flip exTApp t2) (loop e1)

    ExPack mt t1 e2
        -> unop (exPack mt t1) (loop e2)

    ExCast e1 t2 b
        -> unop (flip (flip exCast t2) b) (loop e1)

    _ | Just (k_vars, k_code) <- capture e
        -> (k_vars, k_code $ e +:: k_vars)

      | vars <- []
        -> (vars, e +:: vars)
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
    [ex| $e : $annot |]                 → do
      π ← loop e
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


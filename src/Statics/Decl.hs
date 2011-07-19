{-# LANGUAGE
      ParallelListComp,
      QuasiQuotes,
      TemplateHaskell,
      TupleSections,
      UnicodeSyntax
    #-}
-- | Type checking declarations
module Statics.Decl (
  tcProg, tcDecls, tcDecl
) where

import Util
import qualified AST
import qualified Data.Loc
import Meta.Quasi
import Type
import Statics.Constraint
import Statics.Env as Env
import Statics.Error
import Statics.Type
import Statics.Expr
import Statics.Sealing

import Prelude ()
import Data.IORef (IORef)
import qualified Data.List as List
import qualified Data.Map  as M
import qualified Data.Set  as S

-- | Type check a program
tcProg  ∷ MonadConstraint tv r m ⇒
          Γ tv → AST.Prog R → m (AST.Prog R, Maybe (Type tv))
tcProg γ prog0 = withLocation prog0 $ case prog0 of
  [prQ| $list:ds in $opt:me |]                  → do
    (ds', sig)          ← tcDecls [] γ ds
    meσ'                ← mapM (tcExpr (γ =+= sigToEnv sig)) me
    let me' = fst <$> meσ'
    return ([prQ| $list:ds' in $opt:me' |], snd <$> meσ')

-- | Type check a declaration.
tcDecl  ∷ MonadConstraint tv r m ⇒
          [ModId] → Γ tv → AST.Decl R → m (AST.Decl R, Signature tv)
tcDecl μ γ d0 = withLocation d0 $ case d0 of
  [dc| let $π = $e |]                           → do
    (e', σs)    ← tcExprPatt γ e π
    return ([dc| let $π = $e' |], zipWith SgVal (AST.dv π) σs)
  [dc| type $list:tds |]                        → do
    sig         ← tcTyDecs μ γ tds
    return (d0, sig)
  [dc| abstype $list:at with $list:ds end |]    → do
    (sigC, sigA)        ← tcAbsTys μ γ at
    (ds', sig1)         ← tcDecls μ (γ =+= sigToEnv sigC) ds
    sig                 ← sealWith μ (sigC ++ sig1) (sigA ++ sig1)
    return ([dc| abstype $list:at with $list:ds' end |], sig)
  [dc| module type $sid:n = $sigexp |]          → do
    sig                 ← tcSigExp γ sigexp
    return (d0, [SgSig n sig])
  [dc| module $mid:n = $modexp |]               → do
    (modexp', sig)      ← tcModExp (n:μ) γ modexp
    return ([dc| module $mid:n = $modexp' |], [SgMod n sig])
  [dc| open $modexp |]                          → do
    (modexp', sig) ← tcModExp μ γ modexp
    return ([dc| open $modexp' |], sig)
  [dc| local $list:ds0 with $list:ds1 end |]    → do
    (ds0', sig0) ← tcDecls (AST.ident "?LocalModule":μ) γ ds0
    (ds1', sig1) ← tcDecls μ (γ =+= sigToEnv sig0) ds1
    return ([dc| local $list:ds0' with $list:ds1' end |], sig1)
  [dc| exception $cid:c of $opt:mt |]           → do
    mσ ← toEmptyF <$$> mapM (tcType mempty γ) mt
    return (d0, [SgExn c mσ])
  [dc| $anti:a |]                               → $(AST.antifail)

-- | Type check a sequence of declarations
tcDecls ∷ MonadConstraint tv r m ⇒
          [ModId] → Γ tv → [AST.Decl R] → m ([AST.Decl R], Signature tv)
tcDecls _ _ []     = return ([], [])
tcDecls μ γ (d:ds) = do
  (d', sig0)    ← tcDecl μ γ d
  (ds', sig1)   ← tcDecls μ (γ =+= sigToEnv sig0) ds
  return (d':ds', sig0 ++ sig1)

-- | Type check a module expression
tcModExp ∷ MonadConstraint tv r m ⇒
           [ModId] → Γ tv → AST.ModExp R → m (AST.ModExp R, Signature tv)
tcModExp μ γ modexp0 = withLocation modexp0 $ case modexp0 of
  [meQ| struct $list:ds end |]                  → do
    (ds', sig)          ← tcDecls μ γ ds
    return ([meQ| struct $list:ds' end |], sig)
  [meQ| $qmid:n $list:_ |]                      → do
    (sig, _) ← γ !.! n
    return (modexp0, sig)
  [meQ| $modexp : $sigexp |]                    → do
    (modexp', sig0)     ← tcModExp μ γ modexp
    sig1                ← tcSigExp γ sigexp
    sig                 ← sealWith μ sig0 sig1
    return ([meQ| $modexp' : $sigexp |], sig)
  [meQ| $anti:a |]                              → $(AST.antifail)

-- | Type check a single signature item
tcSigItem ∷ MonadConstraint tv r m ⇒
            Γ tv → AST.SigItem R → m (Signature tv)
tcSigItem γ sigitem0 = withLocation sigitem0 $ case sigitem0 of
  [sgQ| val $vid:n : $t |]                      → do
    σ           ← tcType mempty γ t
    return [SgVal n σ]
  [sgQ| type $list:tds |]                       → tcTyDecs [] γ tds
  [sgQ| module $mid:n : $sigexp |]              → do
    sig         ← tcSigExp γ sigexp
    return [SgMod n sig]
  [sgQ| module type $sid:n = $sigexp |]         → do
    sig         ← tcSigExp γ sigexp
    return [SgSig n sig]
  [sgQ| include $sigexp |]                      → tcSigExp γ sigexp
  [sgQ| exception $cid:c of $opt:mt |]          → do
    mσ ← toEmptyF <$$> mapM (tcType mempty γ) mt
    return [SgExn c mσ]
  [sgQ| $anti:a |]                              → $(AST.antifail)

-- | Type check a signature body
tcSigItems   ∷ MonadConstraint tv r m ⇒
               Γ tv → [AST.SigItem R] → m (Signature tv)
tcSigItems _ []       = return []
tcSigItems γ (sg:sgs) = do
  sig0  ← tcSigItem γ sg
  sig1  ← tcSigItems (γ =+= sigToEnv sig0) sgs
  return (sig0 ++ sig1)

-- | Type check a signature expression
tcSigExp ∷ MonadConstraint tv r m ⇒
           Γ tv → AST.SigExp R → m (Signature tv)
tcSigExp γ sigexp0 = withLocation sigexp0 $ case sigexp0 of
  [seQ| sig $list:sgs end |]                    → tcSigItems γ sgs
  [seQ| $qsid:n $list:_ |]                      → fst <$> γ !.! n
  [seQ| $sigexp with type $list:αs $qtid:qc = $t |]
                                                → do
    sig         ← tcSigExp γ sigexp
    let td      = AST.tdSyn (jname qc) [(AST.tpVar <$> αs <*> pure 1, t)]
    [(_, tc)]   ← tcTyDecs' [] γ [td]
    return (fibrate qc tc sig)
  [seQ| $anti:a |]                              → $(AST.antifail)

-- | Type check the type declarations of an abstype block
tcAbsTys ∷ MonadConstraint tv r m ⇒
           [ModId] → Γ tv → [AST.AbsTy R] →
           m (Signature tv, Signature tv)
tcAbsTys μ γ ats = do
  (arities, quals, tydecs) ← unzip3 <$> mapM unAbsTy ats
  ntcs0                    ← tcTyDecs' μ γ tydecs
  ntcs1 ← sequence
    [ do
        qe ← indexQuals (AST.tdParams (view td)) qual
        return (n, tc {
                     tcArity = arity,
                     tcQual  = qe,
                     tcCons  = mempty,
                     tcNext  = Nothing
                   })
    | (n, tc) ← ntcs0
    | arity   ← arities
    | qual    ← quals
    | td      ← tydecs ]
  return (uncurry SgTyp <$> ntcs0, uncurry SgTyp <$> ntcs1)
  where
    unAbsTy (AST.N _ (AST.AbsTy arity qual td)) = return (arity, qual, td)
    unAbsTy (AST.N _ (AST.AbsTyAnti a))         = $(AST.antifail)

-- | Type check a type declaration group
tcTyDecs  ∷ MonadConstraint tv r m ⇒
            [ModId] → Γ tv → [AST.TyDec R] → m (Signature tv)
tcTyDecs  = uncurry SgTyp <$$$$$> tcTyDecs'

-- | Type check a type declaration group
tcTyDecs' ∷ MonadConstraint tv r m ⇒
            [ModId] → Γ tv → [AST.TyDec R] → m [(TypId, TyCon)]
tcTyDecs' μ γ tds = do
  stub_sig  ← forM tds $ \td → withLocation td $ case view td of
    AST.TdDat tid params _
      → allocStub tid (AST.tvqual <$> params)
    AST.TdSyn tid ((tps,_):_)
      → allocStub tid (Qa <$ tps)
    AST.TdAbs tid params variances guards qual
      → do
        qe ← indexQuals params qual
        ix ← tvUniqueID <$> newTV
        return (tid, mkTC ix (J (reverse μ) tid)
                             qe
                             (zip3 variances
                                   (AST.tvqual <$> params)
                                   ((`elem` guards) <$> params)))
    AST.TdSyn _ []
      → typeBug "tcTyDecs'" "Saw type synonym with 0 clauses."
    AST.TdAnti a
      → $(AST.antifail)
  iterChanging <-> stub_sig $ \sig →
    zipWithM (tcTyDec (γ =+= Env.fromList sig)) tds sig
  where
    allocStub tid bounds = do
      ix ← tvUniqueID <$> newTV
      return (tid, mkTC ix (J (reverse μ) tid)
                           ((Omnivariant,,False) <$> bounds) ∷ TyCon)
    --

tcTyDec ∷ MonadConstraint tv r m ⇒
          Γ tv → AST.TyDec R → (TypId, TyCon) → m (TypId, TyCon)
tcTyDec γ td (tid, tc) = withLocation td $ case view td of
  AST.TdDat _ params alts
    → do
      αs        ← mapM newTV' params
      let δ     = params -:*- αs
      mσs       ← mapM (mapM (tcType δ γ) . snd) alts
      let mσs'          = toEmptyF . closeTy 0 αs <$$> mσs
          arity         = M.findWithDefault 0 <-> ftvV mσs <$> αs
          bounds        = AST.tvqual <$> params
          guards        = M.findWithDefault False <-> ftvG mσs <$> αs
          qual          =
            mapQExp (S.mapMonotonic fromFreeTV) $
              qualifierEnv [bounds] $
                openTy 0 (fvTy <$> [0 ..]) <$> elimEmptyF <$$> mσs'
      when (arity  /= tcArity tc
         || bounds /= tcBounds tc
         || guards /= tcGuards tc
         || qual   /= tcQual tc)
        setChanged
      return (tid, tc {
                     tcArity  = arity,
                     tcBounds = bounds,
                     tcGuards = guards,
                     tcQual   = qual,
                     tcCons   = map fst alts -:*- mσs'
                   })
  AST.TdSyn _ cs@((tps0, _):_)
    → do
      let nparams = length tps0
      tassert (all ((== nparams) . length . fst) cs)
        [msg| In definition of type operator $q:tid, not all clauses
              have the same number of parameters. |]
      (cs', infos) ← unzip <$$> for cs $ \(tps, rhs) → do
        (tps', αss)     ← unzip <$> mapM (tcTyPat γ) tps
        αss'            ← mapM (mapM newTV') αss
        let αs          = concat αss
            αs'         = concat αss'
        σ               ← tcType (αs -:*- αs') γ rhs
        let σ'          = toEmptyF (closeTy 0 αs' σ)
            -- For each pattern, for each of its type variables,
            -- a triple of its variance, inclusion in the qualifer,
            -- and guardedness:
            kindses     = tyPatKinds <$> tps'
            -- The arity of each parameter is the join of the products
            -- of the arities of the type variables in the pattern and
            -- rhs type.
            varmap      = ftvV σ
            arity       = [ bigJoin $
                              zipWith (*)
                                (sel1 <$> kindsi)
                                (M.findWithDefault 0 <-> varmap <$> αsi')
                          | kindsi ← kindses
                          | αsi'   ← αss' ]
            -- How to do bounds? --
            -- This is very permissive:
            guardmap    = ftvG σ
            guards      = [ all2 (||)
                              (M.findWithDefault True <-> guardmap <$> αsi')
                              (sel3 <$> kindsi)
                          | kindsi ← kindses
                          | αsi'   ← αss' ]
            -- For each parameter, a list of which of its type
            -- variables are significant to the qualifier
            qsignificances
                        = [ map snd . filter fst $
                              zip (sel2 <$> kindsi)
                                  αsi'
                          | kindsi ← kindses
                          | αsi'   ← αss' ]
            qual        = case qualifier σ of
              QeA       → QeA
              QeU βs    → bigJoin
               [ case List.findIndex (β `elem`) qsignificances of
                   Nothing → QeA
                   Just ix → qvarexp ix
               | Free β ← S.toList βs ]
        return ((tps', σ'), (arity, guards, qual))
      let (arities, guardses, quals) = unzip3 infos
          arity  = foldl1 (zipWith (⊔)) arities
          guards = foldl1 (zipWith (&&)) guardses
          qual   = bigJoin quals
      when (arity  /= tcArity tc
         || guards /= tcGuards tc
         || qual   /= tcQual tc)
        setChanged
      return (tid, tc {
                     tcArity  = arity,
                     tcGuards = guards,
                     tcQual   = qual,
                     tcNext   = Just cs'
                   })
  AST.TdAbs _ _ _ _ _
    → return (tid, tc)
  AST.TdSyn _ []
    → typeBug "tcTyDec" "Saw type synonym with 0 clauses."
  AST.TdAnti a
    → $(AST.antifail)

-- | Convert a syntactic qualifier expression into an internal
--   qualifier expression over 'Int'.
indexQuals ∷ MonadAlmsError m ⇒
             [AST.TyVar R] → AST.QExp R → m (QExp Int)
indexQuals params = qInterpret resolver where
  resolver tv = case List.findIndex (== tv) params of
    Nothing → typeBug "indexQuals" "tv not found in type params"
    Just ix → return ix

-- | Given a functor, replace the contents with 'Empty', provided
--   there is no contents. If an 'Empty' value is actually required,
--   this is an error.
toEmptyF ∷ Functor f ⇒ f a → f Empty
toEmptyF = fmap toEmpty where
  toEmpty _ = throw (almsBug StaticsPhase "tcDecl" "saw free type variable")

---
--- MODULE SYSTEM
---

-- | Functional update on a signature
fibrate  ∷ QTypId → TyCon → Signature tv → Signature tv
fibrate (J [] tid) tc sig = map eachItem sig where
  eachItem (SgTyp tid' _)
    | tid == tid'       = SgTyp tid tc
  eachItem sigitem      = sigitem
fibrate (J (mid:rest) tid) tc sig = map eachItem sig where
  eachItem (SgMod mid' sig')
    | mid == mid'       = SgMod mid (fibrate (J rest tid) tc sig')
  eachItem sigitem      = sigitem

---
--- TESTING
---

test_tcProg ∷ AST.Prog R →
              IO (Either [AlmsError]
                         (Maybe (Type (TV IORef)),
                          ConstraintState (TV IORef) IORef))
test_tcProg p =
  runConstraintIO
    constraintState0
    (subst =<< snd <$> tcProg test_g0 p)


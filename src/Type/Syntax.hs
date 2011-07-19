{-# LANGUAGE
      FlexibleContexts,
      ParallelListComp,
      PatternGuards,
      UnicodeSyntax
    #-}
-- | For converting internal types back to syntactic types
module Type.Syntax (
  -- * Types to syntax
  typeToStx, typeToStx',
  T2SContext(..), t2sContext0, TyNames(..), tyNames0,
  -- * Patterns to syntax
  tyPatToStx, tyPatToStx',
  -- * Type constructors to type declarations
  tyConToStx, tyConToStx',
) where

import Util
import Util.Trace
import qualified Env
import Type.Internal
import Type.ArrowAnnotations
import Type.TyVar
import qualified AST
import Syntax.PprClass (TyNames(..), tyNames0)

import Prelude ()
import qualified Data.Set as S

type R = AST.Renamed

-- | Context for printing types and type patterns
data T2SContext rule tv
  = T2SContext {
      t2sTyNames  ∷ TyNames,
      t2sArrRule  ∷ rule tv,
      t2sTvEnv    ∷ [[AST.TyVar R]]
    }

-- | The default initial printing context
t2sContext0 ∷ T2SContext CurrentImpArrPrintingRule tv
t2sContext0
  = T2SContext {
      t2sTyNames  = tyNames0,
      t2sArrRule  = iaeInit,
      t2sTvEnv    = []
    }

-- | Represent a type value as a pre-syntactic type, for printing
typeToStx' ∷ Tv tv ⇒ Type tv → AST.Type R
typeToStx' = typeToStx t2sContext0

-- | Turns annotated arrows into implicit arrows where possible
typeToStx ∷ (Tv tv, ImpArrRule rule) ⇒
            T2SContext rule tv → Type tv → AST.Type R
typeToStx cxt0 σ0 = runReader (loop σ0) cxt0 where
  loop (TyVar (Free r)) | debug, Just σ ← unsafeReadTV r =
      do
        δ  ← asks t2sTvEnv
        t  ← loop σ
        return (AST.tyApp (AST.qident "@=")
                          [AST.tyVar (getTV δ (Free r)), t])
      {-
      else throw $
        almsBug (OtherError "unknown")
                "typeToStx"
                ("Saw unsubstituted type variable: " ++ show r)
                -}
  loop (TyVar tv0)           = do
    δ  ← asks t2sTvEnv
    return (AST.tyVar (getTV δ tv0))
  loop (TyQu quant αs σ) =
    withFresh αs $ \αs' → do
      σ' ← loop σ
      return (foldr (AST.tyQu (quantToStx quant)) σ' αs')
  loop (TyMu n σ) =
    withFresh [(n, Qa)] $ \αs' → do
      σ' ← loop σ
      return (foldr AST.tyMu σ' αs')
  loop (TyRow lab σ1 σ2) =
    AST.tyRow lab <$> loop σ1 <*> loop σ2
  loop (TyApp tc [σ1, qe, σ2]) | tc == tcFun = do
    cxt ← ask
    qe' ← represent qe
    let cxt1 = cxt { t2sArrRule = iaeLeft (t2sArrRule cxt) }
        cxt2 = cxt { t2sArrRule = iaeRight (t2sArrRule cxt)
                                           (qualifierCxt cxt qe)
                                           σ1 }
    t1' ← local (\_ → cxt1) (loop σ1)
    t2' ← local (\_ → cxt2) (loop σ2)
    return (AST.tyFun t1' qe' t2')
  loop (TyApp tc σs) = do
    AST.tyApp <$> bestName t2sTyNames tc <*> sequence
      [ local (\cxt → cxt { t2sArrRule = iaeUnder (t2sArrRule cxt) variance })
          (loop σ)
      | σ        ← σs
      | variance ← tcArity tc ]
  --
  withFresh αs k = do
    δ ← asks t2sTvEnv
    let names  = fst <$> αs
        seen   = AST.unLid . AST.tvname <$> concat δ
        names' = AST.freshNames names seen AST.tvalphabet
        αs'    = zipWith3 AST.TV (AST.ident <$> names')
                                 (snd <$> αs)
                                 (repeat AST.bogus)
    local (\cxt → cxt { t2sTvEnv = αs' : δ }) (k αs')
  --
  getTV _ (Free tv)
    = AST.TV (AST.ident (uglyTvName tv)) (fromMaybe Qa (tvQual tv)) AST.bogus
  getTV δ (Bound i j n)
    | rib:_ ← drop i δ, tv:_  ← drop j rib
    = tv
    | otherwise
    = AST.tvAf ('?' : fromPerhaps "" n)
  --
  represent qe = do
    cxt ← ask
    return (iaeRepresent (getTV (t2sTvEnv cxt))
                         (t2sArrRule cxt)
                         (qualifierCxt cxt qe))
  --
  qualifierCxt cxt = qualifierEnv (AST.tvqual <$$> t2sTvEnv cxt)

-- | Represent a type value as a pre-syntactic type, for printing
tyPatToStx' ∷ TyPat → (AST.TyPat R, [AST.TyVar R])
tyPatToStx' = tyPatToStx tyNames0 []

-- | Turn an internal type pattern into a syntactic type pattern
tyPatToStx ∷ TyNames → [(AST.TyVar R, Variance)] → TyPat →
             (AST.TyPat R, [AST.TyVar R])
tyPatToStx tn0 tvs0 tp0 = evalRWS (loop tp0) tn0 (extendTyPatNames tvs0)
  where
  loop (TpVar _)      = fresh AST.tpVar
  loop (TpApp tc tps) = AST.tpApp <$> bestName id tc <*> mapM loop tps
  loop (TpRow _)      = fresh AST.tpRow
  --
  fresh mk = do
    (tv, variance):tvs ← get
    put tvs
    tell [tv]
    return (mk tv variance)

-- | Turn a list of internal type pattern into a list of syntactic type
--   patterns
tyPatsToStx ∷ TyNames → [(AST.TyVar R, Variance)] → [TyPat] →
              ([AST.TyPat R], [AST.TyVar R])
tyPatsToStx tn0 tvs0 tps0 = loop (extendTyPatNames tvs0) tps0 where
  loop _   []       = ([], [])
  loop tvs (tp:tps) =
    let (tp',  tvs')  = tyPatToStx tn0 tvs tp
        (tps', tvss') = loop (drop (length tvs') tvs) tps
     in (tp':tps', tvs'++tvss')

extendTyPatNames ∷ [(AST.TyVar R, Variance)] → [(AST.TyVar R, Variance)]
extendTyPatNames tvs0 =
  tvs0 ++ [ (AST.tvAf name, maxBound)
          | name ← AST.tvalphabet
          , name `notElem` map (AST.unLid . AST.tvname . fst) tvs0 ]

-- | Externalize a quantifier
quantToStx ∷ Quant → AST.Quant
quantToStx Forall = AST.Forall
quantToStx Exists = AST.Exists

-- | Look up the best printing name for a type.
bestName ∷ MonadReader r m ⇒ (r → TyNames) → TyCon → m QTypId
bestName getter tc = do
  tn ← asks getter
  return (tnLookup tn (tcId tc) (tcName tc))

tyConToStx' ∷ TyCon → AST.TyDec R
tyConToStx' = tyConToStx tyNames0

tyConToStx ∷ TyNames → TyCon → AST.TyDec R
tyConToStx tn tc =
  let
  n             = AST.jname (tcName tc)
  tvs           = zipWith3 AST.TV (AST.ident <$> AST.tvalphabet)
                                  (tcBounds tc)
                                  (repeat AST.bogus)
  doType envTvs = typeToStx t2sContext0 { t2sTyNames = tn, t2sTvEnv = [envTvs] }
  in
  case tc of
  _ | tc == tcExn
    → AST.tdAbs (AST.ident "exn") [] [] [] maxBound
  TyCon { tcNext = Just clauses }
    → AST.tdSyn n
                [ second (`doType` rhs) (tyPatsToStx tn [] ps)
                | (ps, rhs) ← clauses ]
  TyCon { tcCons = alts }
    | not (Env.isEmpty alts)
    → AST.tdDat n tvs
                (second (doType tvs <$>) <$> Env.toList alts)
  TyCon { tcArity = arity, tcQual = qual, tcGuards = guards }
    → AST.tdAbs n tvs arity (fst <$> filter snd (zip tvs guards)) $
        case qual of
          QeA     → AST.qeLit Qa
          QeU ixs →
            case fst <$> filter ((`S.member` ixs) . snd) (zip tvs [0..]) of
              []   → AST.qeLit Qu
              tvs' → foldr1 AST.qeJoin (AST.qeVar <$> tvs')



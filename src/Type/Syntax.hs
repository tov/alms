{-# LANGUAGE
      FlexibleContexts,
      ParallelListComp,
      UnicodeSyntax
    #-}
-- | For converting internal types back to syntactic types
module Type.Syntax (
  -- * Types to syntax
  Context(..), typeToStx, typeToStx',
  -- * Patterns to syntax
  tyPatToStx, tyPatToStx',
  -- * Type constructors to type declarations
  tyConToStx, tyConToStx',
) where

import Util
import qualified Env
import Type.Internal
import Type.ArrowAnnotations
import Type.TyVar
import qualified AST
import Syntax.PprClass (TyNames, tyNames0, tnLookup, Ppr(..), showFromPpr)
import Syntax.Ppr ()

import Prelude ()
import qualified Data.Set as S

-- | Context for printing types and type patterns
data Context rule tv
  = Context {
      tyNames  ∷ TyNames,
      arrRule  ∷ rule tv,
      tvEnv    ∷ [[AST.TyVar R]]
    }

-- | The default initial printing context
context0 ∷ Context CurrentImpArrPrintingRule tv
context0
  = Context {
      tyNames  = tyNames0,
      arrRule  = iaeInit,
      tvEnv    = []
    }

-- | Represent a type value as a pre-syntactic type, for printing
typeToStx' ∷ Tv tv ⇒ Type tv → AST.Type R
typeToStx' = typeToStx context0

-- | Turns annotated arrows into implicit arrows where possible
typeToStx ∷ (Tv tv, ImpArrRule rule) ⇒
            Context rule tv → Type tv → AST.Type R
typeToStx cxt0 σ0 = runReader (loop σ0) cxt0 where
  loop (TyVar tv0)           = do
    δ  ← asks tvEnv
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
  loop (TyApp tc [σ1, qe, σ2]) | tc == tcFun =
    AST.tyFun <$> represent qe
              <*> local (\cxt → cxt { arrRule = iaeLeft (arrRule cxt) })
                    (loop σ1)
              <*> local (\cxt → cxt { arrRule = iaeRight (arrRule cxt) (qualifier qe) σ1 })
                    (loop σ2)
  loop (TyApp tc σs) = do
    AST.tyApp <$> bestName tyNames tc <*> sequence
      [ local (\cxt → cxt { arrRule = iaeUnder (arrRule cxt) variance })
          (loop σ)
      | σ        ← σs
      | variance ← tcArity tc ]
  --
  withFresh αs k = do
    δ ← asks tvEnv
    let names  = fst <$> αs
        seen   = AST.unLid . AST.tvname <$> concat δ
        names' = AST.freshNames names seen AST.tvalphabet
        αs'    = zipWith3 AST.TV (AST.lid <$> names')
                                 (snd <$> αs)
                                 (repeat AST.bogus)
    local (\cxt → cxt { tvEnv = αs' : δ }) (k αs')
  --
  getTV _ (Free tv)
    = AST.TV (AST.lid (uglyTvName tv)) (fromMaybe Qa (tvQual tv)) AST.bogus
  getTV δ (Bound i j n)
    | rib:_ ← drop i δ, tv:_  ← drop j rib
    = tv
    | otherwise
    = AST.tvAf ('?' : fromPerhaps "" n)
  --
  represent qe = do
    cxt ← ask
    return (iaeRepresent (getTV (tvEnv cxt)) (arrRule cxt)
                         (qualifierEnv (AST.tvqual <$$> tvEnv cxt) qe))

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
bestName ∷ MonadReader r m ⇒ (r → TyNames) → TyCon → m (AST.QLid R)
bestName getter tc = do
  tn ← asks getter
  return (tnLookup tn (tcId tc) (tcName tc))

tyConToStx' ∷ TyCon → AST.TyDec R
tyConToStx' = tyConToStx tyNames0

tyConToStx ∷ TyNames → TyCon → AST.TyDec R
tyConToStx tn tc =
  let
  n             = AST.jname (tcName tc)
  tvs           = zipWith3 AST.TV (AST.lid <$> AST.tvalphabet)
                                  (tcBounds tc)
                                  (repeat AST.bogus)
  doType envTvs = typeToStx context0 { tyNames = tn, tvEnv = [envTvs] }
  in
  case tc of
  _ | tc == tcExn
    → AST.tdAbs (AST.lid "exn") [] [] [] maxBound
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


instance Tv tv ⇒ Ppr (Type tv) where ppr = ppr . typeToStx'
instance Ppr TyPat where ppr = ppr . fst . tyPatToStx'
instance Ppr TyCon where ppr = ppr . tyConToStx'

instance Tv tv ⇒ Show (Type tv) where showsPrec = showFromPpr
instance Show TyPat where showsPrec = showFromPpr
instance Show TyCon where showsPrec = showFromPpr


module Basis.Row ( entries ) where

import Util
import BasisUtils
import Value
import AST

import qualified Data.Loc

entries :: [Entry Raw]
entries = [
    dec [sgQ| type `a ... |-> `b = {+ (`a -A> `b) ... +} |],
    fun "rowCase" -: [ty| ∀ `a `b. [ `a ] → (`a |-> `b) → `b |]
      -= \variant record → case variant of
           VaLab ix lab v → do
             f ← getField ix lab record
             vapp f v
           _ → throwFailure "case: expected variant",

    fun "isVariant"             -: [ty| ∀ `a. `a → bool |]
      -= \variant → case variant of
           VaLab _ _ _ → True
           _           → False,
    fun "variantLabel"          -: [ty| ∀ `a. [ `a ] → int * string |]
      -= \variant → case variant of
           VaLab ix lab _ → return (ix, show lab)
           _              → throwFailure "variantLabel: not a variant",
    fun "unsafeVariantValue"    -: [ty| ∀ `a `b. [ `a ] → `b |]
      -= \variant → case variant of
           VaLab _ _ v → return v
           _           → throwFailure "variantValue: not a variant",
    fun "unsafeMakeVariant"     -: [ty| ∀ `a `b. int → string → `a → [ `b ] |]
      -= \ix lab v → VaLab ix (ident lab) v,

    fun "isRecord"              -: [ty| ∀ `a. `a → bool |]
      -= \v → do
           case vprjM v of
             Just (AdditiveRecord _)       → True
             Just (MultiplicativeRecord _) → True
             _                             → False,
    fun "isAddRecord"      -: [ty| ∀ `a. `a → bool |]
      -= \v → do
           case vprjM v of
             Just (AdditiveRecord _)       → True
             _                             → False,
    fun "isMulRecord"      -: [ty| ∀ `a. `a → bool |]
      -= \v → do
           case vprjM v of
             Just (MultiplicativeRecord _) → True
             _                             → False,
    fun "recordLabels"          -: [ty| ∀ `a. {+ `a +} → string list |]
      -= \v → do
           record ← vprjM v
           case record of
             AdditiveRecord fields       → map (show . uidToLid . fst) fields
             MultiplicativeRecord fields → map (show . uidToLid . fst) fields,
    fun "unsafeGetRecordField"
          -: [ty| ∀ `a `b. int → string → { `a } → `b |]
      -= \ix lab v → getField ix (lidToUid (ident lab)) v,
    fun "unsafeGetRecordFieldThunk"
          -: [ty| ∀ `a `b. int → string → {+ `a +} → unit → `b |]
      -= \ix lab v → do
           io ← getFieldThunk ix (lidToUid (ident lab)) v
           return (VaFun (FNAnonymous []) (\_ → io)),
    fun "unsafeRecordAddField"
          -: [ty| ∀ `a `b `c. string → `a → { `b } → { `c } |]
      -= \lab v1 v2 → do
           MultiplicativeRecord fields ← vprjM v2
           return . vinj . MultiplicativeRecord $
             (lidToUid (ident lab), v1) : fields
             ∷ IO Value,
    fun "unsafeRecordAddFieldThunk"
          -: [ty| ∀ `a `b `c. string → (unit -A> `a) → {+ `b +} → {+ `c +} |]
      -= \lab thunk v2 → do
           AdditiveRecord fields ← vprjM v2
           return . vinj . AdditiveRecord $
             (lidToUid (ident lab),
              (vapp thunk (vinj ()), vppr thunk)) : fields
             ∷ IO Value,
    fun "unsafeRecordRemoveField"
          -: [ty| ∀ `a `b `q. string → (`q, `a) record → (`q, `b) record |]
      -= \lab v → do
           record ← vprjM v
           return . vinj $ case record of
             AdditiveRecord fields       →
              AdditiveRecord (remField (lidToUid (ident lab)) fields)
             MultiplicativeRecord fields →
              MultiplicativeRecord (remField (lidToUid (ident lab)) fields)
           ∷ IO Value
  ]

getField ∷ Int → Uid Renamed → Value → IO Value
getField = join <$$$> getFieldThunk

getFieldThunk ∷ Int → Uid Renamed → Value → IO (IO Value)
getFieldThunk ix0 lab v = do
  record ← vprjM v
  case record of
    AdditiveRecord fields       → fst <$> findNth ix0 fields
    MultiplicativeRecord fields → return <$> findNth ix0 fields
  where
  findNth _  []         = throwFailure "record field not found"
  findNth ix ((lab', v'):fields')
    | lab == lab'       = if ix == 0
                            then return v'
                            else findNth (ix - 1) fields'
    | otherwise         = findNth ix fields'

remField ∷ Uid Renamed → [(Uid Renamed, v)] → [(Uid Renamed, v)]
remField _ []           = []
remField k ((k',v'):kvs)
  | k == k'             = kvs
  | otherwise           = (k',v') : remField k kvs

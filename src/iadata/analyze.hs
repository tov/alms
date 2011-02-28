{-# LANGUAGE
      UnicodeSyntax
    #-}
module Main where

import Control.Arrow
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

-- | Use this trial to remove duplicates on all the trials.
referenceTrial ∷ [String]
referenceTrial = loadTrial 0

-- | All the trials, duplicates removed
trials   ∷ [[String]]
trials   = [ nub2 referenceTrial (loadTrial ix)
           | ix ← [0 .. 5] ]

-- | Are any pairs of trials the same?
--   Yes: trials!!2 == trials!!3 == trials!!4 == trials!!5
sameTrials ∷ [(Int, Int)]
sameTrials = [ (i, j)
             | i ← [0 .. length trials - 1]
             , j ← [i + 1 .. length trials - 1]
             , trials!!i == trials!!j ]

-- | Number of types per trial
ntypes   ∷ Int
ntypes   = length (trials !! 0)

-- | Does the given type somewhere contain a function arrow?
hasArrowType ∷ String → Bool
hasArrowType = elem '>'

-- | Extract the arrow annotations from a type
annotationsOf ∷ String → [String]
annotationsOf t = case t of
  '-':rest     → takeWhile (/='>') rest : annotationsOf (skip rest)
  _:rest       → annotationsOf rest
  []           → []
  where skip rest = case dropWhile (/='>') rest of
          '>':rest' → rest'
          _         → error t

-- | Retain only the types with arrows, and retain only the annotations
--   of those.
annotations ∷ [[(String, [String])]]
annotations = map (map (id &&& annotationsOf) . filter hasArrowType) trials

-- | Types that have annotations
anntypes    ∷ [[(String, [String])]]
anntypes    = map (filter (any (not . null) . snd)) annotations

-- | Number of non-trivial (arrow-containing) types
nanntypes   ∷ [Int]
nanntypes   = map length anntypes

-- | A flat list of the annotations for each trial.
flatAnnotations ∷ [[String]]
flatAnnotations = map (concatMap snd) annotations

-- | Number of arrows (and thus potential annotations)
narrows     ∷ Int
narrows     = length (flatAnnotations !! 0)

-- | Number of annotations per trial
nannotations ∷ [Int]
nannotations = map (length . filter (/="")) flatAnnotations

-- | All types and their annotations in dst that are different or
--   absent in src
diffAnnotations ∷ Int → Int → [((String, [String]), (String, [String]))]
diffAnnotations src dst =
  [ ((τ1, φs1), (τ2, φs2))
  | ((τ1, φs1), (τ2, φs2)) ← zip (annotations!!src) (annotations!!dst)
  , any (\(φ1,φ2) → φ1 /= φ2 && φ2 /= "") (zip φs1 φs2)
  ]

-- | Remove elements from second list corresponding to repeats from
--   first.
nub2 ∷ Ord a ⇒ [a] → [b] → [b]
nub2 = loop Set.empty where
  loop seen (x:xs) (y:ys)
    | x `Set.member` seen = loop seen xs ys
    | otherwise           = y : loop (Set.insert x seen) xs ys
  loop _    []     [] = []
  loop _    []     _  = error "nub2: second argument is longer"
  loop _    _      [] = error "nub2: first argument is longer"

-- | Load the data for a given trial number.
loadTrial    ∷ Int → [String]
loadTrial ix =
  loadFile (makeFileName ix False) ++ loadFile (makeFileName ix True)

-- Load a file as a list of strings.
loadFile     ∷ String → [String]
loadFile     = lines . unsafePerformIO . readFile

-- | Given a trial number and a boolean designating library or builtin
--   types, constructs the file name holding that trial's data.
makeFileName ∷ Int → Bool → String
makeFileName ix lib =
  "iadata" ++ show ix ++ if lib then ".lib" else ".builtin"

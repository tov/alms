{-# LANGUAGE
      PatternGuards #-}
-- Miscellaneous high-level printing routines.  These can't go in, say,
-- Ppr, because they depend on Rename and Statics.
module Printing (
  addTyNameContext
) where

import Data.List (tails)
import PprClass
import Rename (RenameState, RenamingInfo(..),
               getRenamingInfo, renamingEnterScope)
import Statics (S, getTypeInfo, staticsEnterScope)
import AST.Ident
import Type
import Util

-- | The status of a type name in an environment
data NameStatus
 -- | Bound to the expected type
 = Match
 -- | Not bound
 | NoMatch
 -- | Shadowed
 | Interfere
 deriving Eq

-- | In the given environment, what is the status of the given
--   type name?
getNameStatus :: RenameState -> S -> Int -> QLid i -> NameStatus
getNameStatus r s tag ql =
  case [ ql' | TyconAt _ ql' <- getRenamingInfo ident r ] of
    ql':_ ->
      case getTypeInfo ql' s of
        Just tc | tcId tc == tag  -> Match
                | otherwise       -> Interfere
        _                         -> NoMatch
    _     -> NoMatch
  where ident = J (map (uid . unUid) (jpath ql))
                  (Var (lid (unLid (jname ql))))

-- | Find the best name to refer to a type constructor.
--   The goal here is to get the shortest unambiguous name.
--    1. If the first parameter is True, we want an accurate name, so
--       skip to step 3.
--    2. If the unqualified name is bound to either the same type
--       or to nothing, then use the unqualified name.
--    3. Try qualifiying the name, starting with the last segment
--       and adding one at a time, and if any of these match, then
--       use that.
--    4. Otherwise, uglify the name, because it's probably gone
--       out of scope.
getBestName :: RenameState -> S ->
               Int -> QLid Renamed -> QLid Renamed
getBestName r s tag ql =
  case tryQuals (jpath ql) (jname ql) of
    Just ql' -> ql'
    _ | isTrivial (lidUnique (jname ql)),
        NoMatch <- getNameStatus r s tag ql
             -> ql
    _        -> uglify
  where
    tryQuals us l = msum
      [ case getNameStatus r s tag (J us' l) of
          Match     -> Just (J us' l)
          _         -> Nothing
      | us' <- reverse (tails us) ]
    uglify = ql { jpath = uid ('?':show tag) : jpath ql }

makeTyNames :: RenameState -> S -> TyNames
makeTyNames r s = TyNames {
  tnLookup = getBestName r s,
  tnEnter  = \u -> makeTyNames (renamingEnterScope u r)
                               (staticsEnterScope u s)
}

addTyNameContext :: RenameState -> S -> Doc -> Doc
addTyNameContext  = setTyNames <$$> makeTyNames

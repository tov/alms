{-# LANGUAGE
      TemplateHaskell #-}
-- | Compatibility layer for different GHC and library versions
module Compat (
  mask, newQuasi,
) where

import Language.Haskell.TH

import Language.Haskell.TH.Quote
import qualified Control.Exception

mask :: ((IO a -> IO a) -> IO b) -> IO b
mask  = $(do
  let name s = mkName ("Control.Exception." ++ s)
      var    = varE . name
  recover
    [| \action -> do
         b <- $(var "blocked")
         let restore = if b then $(var "block")
                            else $(var "unblock")
         $(var "block") (action restore) |]
    (do reify (name "mask")
        [| \action -> $(var "mask") (\restore -> action restore) |]))

newQuasi :: String -> QuasiQuoter
newQuasi name = $(do
  let quasiQuoter = conE 'QuasiQuoter
      arity (AppT (AppT ArrowT _) t') = 1 + arity t'
      arity _                         = 0 :: Int
  DataConI _ ty _ _ <- reify 'QuasiQuoter
  [| let qf cat _ = fail $ "Quasiquoter ‘" ++ name ++
                           "’ does not support " ++ cat
         q2       = $quasiQuoter (qf "expressions") (qf "patterns") in
       $(if arity ty == 4
           then [| q2 (qf "types") (qf "declarations") |]
           else [| q2 |]) |])



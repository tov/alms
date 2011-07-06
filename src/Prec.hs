-- | Operator precdences
--
-- We use operator precedences from Ocaml.  The precence and
-- associativity of an operator is determined by its first character.
module Prec (
  Prec, precOp, fixities,
  -- * Precedences for reserved operators needed by the parser
  precMin, precStart, precMax, precCast,
  precCom, precDot, precExSemi, precTySemi, precEq, precCaret, precArr,
  precPlus, precStar, precAt, precApp, precBang,
) where

import Data.Char

-- | Precedence and associativity, e.g. @Right 4@ is right-associative
--   at level 4.  Higher precedences bind tighter, with application
--   at precedence 9.
type Prec = Either Int Int

precOp :: String -> Prec
precOp ('*':'*':_)    = Right precAt
precOp ('→':_)        = Right precArr
precOp ('-':'>':_)    = Right precArr
precOp ('-':'o':_)    = Right precArr
precOp "-[]>"         = Right precArr
precOp (';':_)        = Right precTySemi
precOp "⋁"            = Right precTySemi
precOp "\\/"          = Right precTySemi
precOp "!="           = Left precEq
precOp (c:cs)
  | c `elem` "=<>|&$" = Left precEq
  | c `elem` "*×/%"   = Left precStar
  | c `elem` "+-"     = Left precPlus
  | c `elem` "^"      = Right precCaret
  | c `elem` "@"      = Right precAt
  | c `elem` "!~?"    = Right precBang
  | otherwise = case generalCategory c of
      CurrencySymbol        -> Left precEq
      MathSymbol            -> Left precStar
      DashPunctuation       -> Left precPlus
      OtherSymbol           -> Left precPlus
      ConnectorPunctuation  -> Right precCaret
      OtherPunctuation      -> Right precAt
      _                     -> precOp cs
precOp ""             = Left precApp

precMin, precStart, precMax, precCast,
  precCom, precDot, precExSemi, precTySemi, precEq, precCaret, precArr,
  precPlus, precStar, precAt, precApp, precBang :: Int
precMin   = -1
precCom   = -1 -- ,
precStart =  0 -- includes "|" for row types
precDot   =  1 -- in, else, of, .
precExSemi=  1 -- ;  (expressions only)
precCast  =  2 -- :>
precArr   =  3 -- ->
precEq    =  5 -- != = < > | & $ as
precCaret =  5 -- ^ (infixr)
precPlus  =  6 -- - +
precStar  =  7 -- % / *
precTySemi=  8 -- ; "\\/" "⋁" (types only)
precAt    =  9 -- @ ** (infixr)
precApp   = 10 -- f x
precBang  = 11 -- ! ~ ? (prefix)
precMax   = 11

{-# INLINE fixities #-}
-- To find out the fixity of a precedence level
fixities :: Int -> Maybe Prec
fixities n
  | n == precArr    = Just $ Right precArr
  | n == precEq     = Just $ Left precEq
  | n == precCaret  = Just $ Right precCaret
  | n == precPlus   = Just $ Left precPlus
  | n == precStar   = Just $ Left precStar
  | n == precTySemi = Just $ Right precTySemi
  | n == precAt     = Just $ Right precAt
  | n == precBang   = Just $ Right precBang
  | otherwise       = Nothing

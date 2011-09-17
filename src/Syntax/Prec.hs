-- | Operator precdences
--
-- We use operator precedences from Ocaml.  The precence and
-- associativity of an operator is determined by its first character.
module Syntax.Prec (
  Prec, precOp, fixities,
  -- * Precedences for reserved operators needed by the parser
  precMin, precStart, precMax, precCast,
  precCom, precDot, precExSemi, precTySemi, precEq, precCaret, precArr,
  precOr, precAnd, precPlus, precStar, precAt, precApp, precBang, precSel,
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
precOp ('←':_)        = Right precArr
precOp ('<':'-':_)    = Right precArr
precOp (':':'=':_)    = Right precArr
precOp "||"           = Right precOr
precOp "&&"           = Right precAnd
precOp "-[]>"         = Right precArr
precOp (';':_)        = Right precTySemi
precOp "⋁"            = Right precTySemi
precOp "\\/"          = Right precTySemi
precOp "!="           = Left precEq
precOp (c:cs)
  | c `elem` "=<>|&$" = Left precEq
  | c `elem` "*×/%"   = Left precStar
  | c `elem` "+-"     = Left precPlus
  | c `elem` "^:∷"    = Right precCaret
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
  precOr, precAnd,
  precPlus, precStar, precAt, precApp, precSel, precBang :: Int
precMin   = -1
precCom   = -1 -- ,
precStart =  0 -- includes "|" for row types
precDot   =  1 -- in, else, of, .
precExSemi=  1 -- ;  (expressions only)
precCast  =  2 -- :>
precArr   =  3 -- ->… →… <-… ←… :=…
precOr    =  4 -- ||…
precAnd   =  5 -- & &&…
precEq    =  6 -- !=… =… <… >… |… &… $… as…
precPlus  =  7 -- -… +;…
precCaret =  8 -- ^… :… ∷… (infixr)
precStar  =  9 -- %… /… *…
precTySemi= 10 -- ; "\\/" "⋁" (types only)
precAt    = 11 -- @… **… (right)
precApp   = 12 -- f x
precSel   = 13 -- record selection
precBang  = 14 -- !… ~… ?… (prefix)
precMax   = 14

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

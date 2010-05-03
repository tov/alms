-- | Operator precdences
--
-- We use operator precedences from Ocaml.  The precence and
-- associativity of an operator is determined by its first character.
module Prec (
  Prec, precOp,
  -- * Precedences for reserved operators needed by the parser
  precMin, precStart, precMax,
  precCast, precCom, precDot, precSemi, precEq, precAt, precArr,
  precPlus, precStar, precExp, precApp, precBang, precTApp
) where

-- | Precedence and associativity, e.g. @Right 4@ is right-associative
--   at level 4.  Higher precedences bind tighter, with application
--   at precedence 9.
type Prec = Either Int Int

precOp :: String -> Prec
precOp ('*':'*':_)    = Right precExp
precOp ('-':'>':_)    = Right precArr
precOp ('-':'o':_)    = Right precArr
precOp "-[]>"         = Right precArr
precOp (';':_)        = Right precSemi
precOp "!="           = Left precEq
precOp (c:_)
  | c `elem` "=<>|&$" = Left precEq
  | c `elem` "*/%"    = Left precStar
  | c `elem` "+-"     = Left precPlus
  | c `elem` "@^"     = Right precAt
  | c `elem` "!~?"    = Right precBang
precOp _              = Left precApp

precMin, precStart, precMax,
  precCast, precCom, precDot, precSemi, precEq, precAt, precArr,
  precPlus, precStar, precExp, precApp, precBang, precTApp :: Int
precMin   = -2
precCast  = -2 -- :>
precCom   = -1 -- ,
precStart =  0
precDot   =  1 -- in, else, as, of, .
precArr   =  2 -- ->
precEq    =  3 -- != = < > | & $
precAt    =  4 -- @ ^ (infixr)
precPlus  =  5 -- - +
precStar  =  6 -- % / *
precSemi  =  7 -- ;  (types only)
precExp   =  8 -- ** (infixr)
precApp   =  9 -- f x
precBang  = 10 -- ! ~ ? (prefix)
precTApp  = 11 -- f[t]
precMax   = 11

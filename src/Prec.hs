-- | Operator precdences
--
-- We use operator precedences from Ocaml.  The precence and
-- associativity of an operator is determined by its first character.
module Prec (
  Prec, precOp,
  -- * Precedences for reserved operators needed by the parser
  precSemi, precCom, precDot, precArr, precStar, precApp, precCast, precTApp
) where

-- | Precedence and associativity, e.g. @Right 4@ is right-associative
--   at level 4.  Higher precedences bind tighter, with application
--   at precedence 9.
type Prec = Either Int Int

precOp :: String -> Prec
precOp ('*':'*':_)    = Right 7
precOp (c:_)
  | c `elem` "*/%"    = Left 6
  | c `elem` "+-"     = Left 5
  | c `elem` "@^"     = Right 4
  | c `elem` "=<>|&$" = Left 3
precOp "!="           = Left 3
precOp (c:_)
  | c `elem` "!~?"    = Right 10
precOp _              = Left 9

precCast, precCom, precDot, precSemi, precArr, precStar,
  precApp, precTApp :: Int
precCast  = -2 -- :>
precCom   = -1 -- ,
precDot   =  0 -- in, else, as, of, .
precSemi  =  1 -- ;
--           3 -- != = < > | & $
--           4 -- @ ^ (infixr)
precArr   =  5 -- -> - +
precStar  =  6 -- % / *
--           7 -- ** (infixr)
precApp   =  9 -- f x
--          10 -- ! ~ ? (prefix)
precTApp  = 11 -- f[t]


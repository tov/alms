{-# LANGUAGE
      CPP,
      UnicodeSyntax
    #-}
-- | Hard-coded strings that depend on whether we're doing unicode.
module Syntax.Strings where

{-# INLINE digits #-}
-- | Subscript numerals for type variables
digits ∷ [Char]

{-# INLINE tvNames #-}
-- | Names to give to type variables
tvNames ∷ [Char]

{-# INLINE fun #-}
{-# INLINE arrow #-}
-- | Term keywords
fun, arrow ∷ String

{-# INLINE all #-}
{-# INLINE ex #-}
{-# INLINE mu #-}
-- | Quantifiers
all, ex, mu ∷ String

{-# INLINE uArrow #-}
{-# INLINE aArrow #-}
{-# INLINE arrowPre #-}
{-# INLINE arrowPost #-}
{-# INLINE join #-}
-- | Infix type constructors
uArrow, aArrow, arrowPre, arrowPost, join ∷ String

{-# INLINE affine #-}
{-# INLINE unlimited #-}
{-# INLINE covariant #-}
{-# INLINE contravariant #-}
{-# INLINE invariant #-}
{-# INLINE omnivariant #-}
{-# INLINE qcovariant #-}
{-# INLINE qcontravariant #-}
{-# INLINE qinvariant #-}
-- | Sigils
affine, unlimited,
  covariant, contravariant, invariant, omnivariant,
  qcovariant, qcontravariant, qinvariant ∷ String

{-# INLINE ellipsis #-}
ellipsis ∷ String

#ifdef UNICODE
digits = unicodeDigits
tvNames         = [ 'a' .. 'z' ]
all             = "∀"
ex              = "∃"
mu              = "μ"
product         = "×"
uArrow          = "→"
aArrow          = "-A>"
arrowPre        = "-"
arrowPost       = ">"
join            = "⋁"
affine          = "`"
unlimited       = "\'"
covariant       = "+"
contravariant   = "-"
invariant       = ""
omnivariant     = "0"
qcovariant      = "Q+"
qcontravariant  = "Q-"
qinvariant      = "Q"
ellipsis        = "..."
fun             = "λ"
arrow           = "→"
#else
digits = asciiDigits
tvNames         = [ 'a' .. 'z' ]
all             = "all"
ex              = "ex"
mu              = "mu"
product         = "*"
uArrow          = "->"
aArrow          = "-A>"
arrowPre        = "-"
arrowPost       = ">"
join            = "\\/"
affine          = "`"
unlimited       = "\'"
covariant       = "+"
contravariant   = "-"
invariant       = ""
omnivariant     = "0"
qcovariant      = "Q+"
qcontravariant  = "Q-"
qinvariant      = "Q"
ellipsis        = "..."
fun             = "fun"
arrow           = "->"
#endif

{-# INLINE unicodeDigits #-}
{-# INLINE asciiDigits #-}
unicodeDigits, asciiDigits ∷ [Char]
unicodeDigits = "₀₁₂₃₄₅₆₇₈₉"
asciiDigits   = "0123456789"

normalizeChar ∷ Char → Char
normalizeChar '₀' = '0'
normalizeChar '₁' = '1'
normalizeChar '₂' = '2'
normalizeChar '₃' = '3'
normalizeChar '₄' = '4'
normalizeChar '₅' = '5'
normalizeChar '₆' = '6'
normalizeChar '₇' = '7'
normalizeChar '₈' = '8'
normalizeChar '₉' = '9'
normalizeChar '′' = '\''
normalizeChar 'α' = 'a'
normalizeChar 'β' = 'b'
normalizeChar 'ψ' = 'c'
normalizeChar 'δ' = 'd'
normalizeChar 'ε' = 'e'
normalizeChar 'φ' = 'f'
normalizeChar 'γ' = 'g'
normalizeChar 'η' = 'h'
normalizeChar 'ι' = 'i'
normalizeChar 'ξ' = 'j'
normalizeChar 'κ' = 'k'
normalizeChar 'λ' = 'l'
normalizeChar 'μ' = 'm'
normalizeChar 'ν' = 'n'
normalizeChar 'ο' = 'o'
normalizeChar 'π' = 'p'
normalizeChar 'ρ' = 'r'
normalizeChar 'σ' = 's'
normalizeChar 'τ' = 't'
normalizeChar 'θ' = 'u'
normalizeChar 'ω' = 'v'
normalizeChar 'ς' = 'w'
normalizeChar 'χ' = 'x'
normalizeChar 'υ' = 'y'
normalizeChar 'ζ' = 'z'
normalizeChar c   = c


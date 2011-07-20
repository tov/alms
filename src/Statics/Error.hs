-- | Type errors
module Statics.Error (
  -- * Basic error functions
  typeBug, typeBugError, typeError, typeError_, typeError', tassert,

  -- * Messages
  gotMessage, expMessage,
  -- ** Specialized message functions
  tErrGot, tErrGot_, tErrGot', tAssGot,
  tErrExp, tErrExp_, tErrExp', tAssExp,

  -- * Re-exports
  module Error,
) where

import Util
import Error
import Type

import Prelude ()

-- | Indicate a bug in the type checker.
typeBug         ∷ MonadAlmsError m ⇒ String → String → m a
typeBug         = throwAlms <$$> almsBug StaticsPhase

-- | Indicate a bug in the type checker, with no Alms error monad.
typeBugError    ∷ String → String → a
typeBugError    = throw <$$> almsBug StaticsPhase

-- | Indicate a type error.
typeError       ∷ (MonadAlmsError m, Bogus a) ⇒ Message V → m a
typeError msg0  = do
  reportAlms (AlmsError StaticsPhase bogus msg0)
  return bogus

-- | Indicate a type error.
typeError_      ∷ MonadAlmsError m ⇒ Message V → m ()
typeError_      = typeError

-- | Indicate a type error from which we cannot recover.
typeError'      ∷ MonadAlmsError m ⇒ Message V → m a
typeError'      = throwAlms <$> AlmsError StaticsPhase bogus

-- | Assert some condition, indicating a type error if it doesn't hold.
tassert         ∷ MonadAlmsError m ⇒ Bool → Message V → m ()
tassert True _  = return ()
tassert False m = typeError m

-- | Common message pattern: A got B where C expected
gotMessage      ∷ Tv tv ⇒ String → Type tv → String → Message V
gotMessage who got expected =
  [msg| $words:who got $q:got where $words:expected expected. |]

-- | Error for 'gotMessage'
tErrGot         ∷ (MonadAlmsError m, Bogus a, Tv tv) =>
                  String -> Type tv -> String -> m a
tErrGot         = typeError <$$$> gotMessage

-- | Error for 'gotMessage'
tErrGot_        ∷ (MonadAlmsError m, Tv tv) =>
                  String -> Type tv -> String -> m ()
tErrGot_        = tErrGot

-- | Stopping error for 'gotMessage'
tErrGot'        ∷ (MonadAlmsError m, Tv tv) =>
                  String -> Type tv -> String -> m a
tErrGot'        = typeError' <$$$> gotMessage


-- | Assertion for 'gotMessage'
tAssGot         ∷ (MonadAlmsError m, Tv tv) =>
                  Bool -> String -> Type tv -> String -> m ()
tAssGot True    = \_ _ _ → return ()
tAssGot False   = tErrGot

-- | Common message pattern, actual vs. expected
expMessage      ∷ Message V → Message V → Message V → Message V
expMessage      =
  [msg|
    $msg:1
    <dl>
      <dt>actual:   <dd>$msg:2
      <dt>expected: <dd>$msg:3
    </dl>
  |]

-- | Error for 'expMessage'
tErrExp         ∷ (MonadAlmsError m, Bogus a) ⇒
                  Message V → Message V → Message V → m a
tErrExp         = typeError <$$$> expMessage

-- | Error for 'expMessage'
tErrExp_        ∷ MonadAlmsError m ⇒
                  Message V → Message V → Message V → m ()
tErrExp_        = tErrExp

-- | Stopping error for 'expMessage'
tErrExp'        ∷ (MonadAlmsError m) ⇒
                  Message V → Message V → Message V → m a
tErrExp'        = typeError' <$$$> expMessage

-- | Assertion for 'expMessage'
tAssExp         ∷ MonadAlmsError m ⇒
                  Bool → Message V → Message V → Message V → m ()
tAssExp True    = \_ _ _ → return ()
tAssExp False   = tErrExp


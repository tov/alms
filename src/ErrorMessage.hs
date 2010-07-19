{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      QuasiQuotes
      #-}
module ErrorMessage (
  AlmsException(..), Phase(..), AlmsMonad(..),
  almsBug, (!::),
  module Message.Quasi
) where

import Loc
import PprClass
import Message.AST
import Message.Render ()
import Message.Quasi

import Data.Typeable (Typeable)
import Control.Exception (Exception, throwIO, catch)
import Control.Monad.Error (Error(..))

--
-- Representation of Alms errors
--

-- | Alms internal exceptions
data AlmsException
  = AlmsException {
      exnPhase   :: Phase,    -- | When did it happen?
      exnLoc     :: Loc,      -- | Where in the source did it happen?
      exnMessage :: Message V -- | What happened?
  }
  deriving Typeable

-- | The phases in which an error might occur:
data Phase
  = ParserPhase
  | RenamerPhase
  | StaticsPhase
  | DynamicsPhase
  | OtherError String
  deriving Show

-- | Error constructors

almsBug :: Phase -> Loc -> String -> String -> AlmsException
almsBug phase loc culprit0 msg0 =
  let culprit = if null culprit0
                  then "unknown"
                  else culprit0 in
  AlmsException (OtherError "BUG! in Alms implementation")
                bogus
                [$msg|
                  This shouldn’t happen, so it probably
                  indicates a bug in the Alms implementation.
                  <p>
                  Details:
                  <dl>
                    <dt>who:  <dd>$words:culprit
                    <dt>what: <dd>$words:msg0
                    <dt>where:<dd>$show:loc
                    <dt>when: <dd>$show:phase
                  </dl>
                  <p>
                  Please report to <exact><tov@ccs.neu.edu></exact>.
                |]

(!::) :: Show a => String -> a -> Message d
msg0 !:: thing = [$msg| $words:msg0 <q>$show:thing</q> |]
infix 1 !::

---
--- The AlmsMonad class for carrying alms errors
---

class Monad m => AlmsMonad m where
  throwAlms :: AlmsException -> m a
  catchAlms :: m a -> (AlmsException -> m a) -> m a
  unTryAlms :: m (Either AlmsException a) -> m a
  unTryAlms  = (>>= either throwAlms return)

instance AlmsMonad IO where
  throwAlms = throwIO
  catchAlms = Control.Exception.catch

instance AlmsMonad (Either AlmsException) where
  throwAlms = Left
  catchAlms (Right a) _ = Right a
  catchAlms (Left e)  k = k e

---
--- Instances
---

instance Ppr AlmsException where
  ppr (AlmsException phase loc msg0) =
     (text phaseString <+> locString <> colon)
     $$
     ppr (Indent msg0)
     where locString   = if isBogus loc
                           then empty
                           else text "at" <+> text (show loc)
           phaseString = case phase of
             ParserPhase   -> "Syntax error"
             RenamerPhase  -> "Type error"
             StaticsPhase  -> "Type error"
             DynamicsPhase -> "Run-time error"
             OtherError s  -> s

instance Show AlmsException where showsPrec = showFromPpr

instance Exception AlmsException

instance Error AlmsException where
  strMsg = AlmsException (OtherError "Error") bogus . Block . Words

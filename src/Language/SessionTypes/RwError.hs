{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.SessionTypes.RwError
  ( Error(..)
  ) where

import Language.SessionTypes

import Control.Monad.Except

data Error
  = MultiChoice [Role] Role
  | EmptySubstitution

instance MonadError Error Maybe where
  throwError _ = Nothing
  catchError (Just x) _f =  Just x
  catchError Nothing   f = f EmptySubstitution -- XXX: Hack!!!

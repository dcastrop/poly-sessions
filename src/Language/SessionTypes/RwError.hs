{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.SessionTypes.RwError
  ( Error(..)
  ) where

import Language.SessionTypes.Common
import Language.SessionTypes.Prefix.Global
import Language.Poly.C

import Control.Monad.Except

data Error
  = MultiChoice [Role] Role
  | InvalidSubst Role [Role]
  | EmptySubstitution
  | IllTypedAnn (Msg CType ECore)
  | UnknownError

instance MonadError Error Maybe where
  throwError _ = Nothing
  catchError (Just x) _f =  Just x
  catchError Nothing   f = f UnknownError -- XXX: Hack!!!

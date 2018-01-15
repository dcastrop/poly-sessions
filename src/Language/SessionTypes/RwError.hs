module Language.SessionTypes.RwError
  ( Error(..)
  ) where

import Language.SessionTypes

data Error
  = MultiChoice [Role] Role
  | EmptySubstitution

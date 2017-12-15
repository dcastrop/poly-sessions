module Language.SessionTypes.RwSession
( CCore
, Lbl (..)
, ParSession
) where

import Language.Internal.Id
import Language.Poly.C
import Language.SessionTypes

data Lbl = Lbl { lblname :: String, lblpre :: CCore, lblpost :: CCore }

type ParSession = GT Id CType Lbl

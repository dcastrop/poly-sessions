-- Wrapper on top of Language.Poly + C-like expressions
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Poly.C
  ( PrimTy (..)
  , TyPrim (..)
  , C
  , CInt
  , CFloat
  , CNum
  , CType
  , CExpr (..)
  , CCore
  , ECore (..)
  , module X
  ) where

import Data.Singletons
  ( SingI (..)
  , SingKind(..)
  , SomeSing(..) )
import Data.Singletons.TypeLits as Sing

import Language.Poly as X

-- Primitive functions and operations
data TyPrim = TInt32 | TFloat32 | TVector Sing.Nat TyPrim
data PrimTy = Int32  | Float32  | Vector Integer PrimTy

data instance Sing (t :: TyPrim) where
    SInt32 :: Sing 'TInt32
    SFloat32 :: Sing 'TFloat32
    SVector :: Sing i -> Sing t -> Sing ('TVector i t)
instance SingI 'TInt32 where
  sing = SInt32
instance SingI 'TFloat32 where
  sing = SFloat32
instance (SingI i, SingI t) => SingI ('TVector i t) where
  sing = SVector sing sing

instance SingKind TyPrim where
  type DemoteRep TyPrim = PrimTy
  fromSing SInt32 = Int32
  fromSing SFloat32 = Float32
  fromSing (SVector i t) = Vector (fromSing i) (fromSing t)
  toSing Int32 = SomeSing SInt32
  toSing Float32 = SomeSing SFloat32
  toSing (Vector (toSing -> SomeSing i) (toSing -> SomeSing t)) =
      SomeSing $ SVector i t

type family C (a :: TyPrim) :: Type TyPrim where
  C a = 'TPrim a

type CInt   = C 'TInt32
type CFloat = C 'TFloat32

class CNum (a :: TyPrim) where
instance CNum 'TInt32 where
instance CNum 'TFloat32 where

type CType = Type PrimTy

data CExpr (t :: Type TyPrim) where
    Plus  :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Minus :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Mult  :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Div   :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Mod   :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Get   :: CExpr (C ('TVector i a) ':-> CInt ':-> C a)
    Put   :: CExpr (CInt ':-> C a ':-> C ('TVector i a) ':-> C ('TVector i a))

type CCore = Core CExpr

data ECore where
    EIdle :: ECore
    EEval :: forall (t :: Type TyPrim). Sing t -> CCore t -> ECore

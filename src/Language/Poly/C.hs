-- Wrapper on top of Language.Poly + C-like expressions
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE QuasiQuotes #-}
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
  , getDom
  , getCod
  , module X
  ) where

import Data.Singletons
  ( SingI (..)
  , SingKind(..)
  , SomeSing(..) )
import Data.Singletons.TypeLits as Sing

import Data.Text.Prettyprint.Doc ( Pretty, pretty )
import Data.Text.Prettyprint.EDoc

import Language.Poly as X
import Language.Poly.Erasure ( Erasure (..) )
import Language.Poly.UCore()

-- Primitive functions and operations
data TyPrim = TInt32 | TFloat32 | TVector Sing.Nat TyPrim
data PrimTy = Int32  | Float32  | Vector Integer PrimTy
  deriving (Eq, Show)

instance Pretty PrimTy where
  pretty t = [ppr| show t |]

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
    CInt  :: Int -> CExpr CInt
    Plus  :: CNum a => CExpr ('TProd (C a) (C a) ':-> C a)
    Minus :: CNum a => CExpr ('TProd (C a) (C a) ':-> C a)
    Mult  :: CNum a => CExpr ('TProd (C a) (C a) ':-> C a)
    Div   :: CNum a => CExpr ('TProd (C a) (C a) ':-> C a)
    Mod   :: CNum a => CExpr ('TProd (C a) (C a) ':-> C a)
    Get   :: CExpr ('TProd (C ('TVector i a)) CInt ':-> C a)
    Put   :: CExpr ('TProd ('TProd CInt (C a)) (C ('TVector i a))
                   ':-> C ('TVector i a))

data UCExpr t where
    UCInt  :: Int -> UCExpr t
    UPlus  :: UCExpr t
    UMinus :: UCExpr t
    UMult  :: UCExpr t
    UDiv   :: UCExpr t
    UMod   :: UCExpr t
    UGet   :: UCExpr t
    UPut   :: UCExpr t
    deriving Eq

instance Pretty (UCExpr PrimTy) where
  pretty (UCInt i) = [ppr| i|]
  pretty UPlus     = [ppr| "plus" |]
  pretty UMinus    = [ppr| "minus" |]
  pretty UMult     = [ppr| "mult" |]
  pretty UDiv      = [ppr| "div" |]
  pretty UMod      = [ppr| "mod" |]
  pretty UGet      = [ppr| "get" |]
  pretty UPut      = [ppr| "put" |]

instance Erasure TyPrim CExpr UCExpr where
  erase (CInt i) = UCInt i
  erase Plus  = UPlus
  erase Minus = UMinus
  erase Mult  = UMult
  erase Div   = UDiv
  erase Mod   = UMod
  erase Get   = UGet
  erase Put   = UPut

type CCore = Core CExpr

data ECore where
    EIdle :: ECore
    EEval :: forall (t :: Type TyPrim). Sing t -> CCore t -> ECore

instance Pretty ECore where
  pretty EIdle = [ppr| "idle" |]
  pretty (EEval _ c)= [ppr| c |]

instance Eq ECore where
  EIdle       == EIdle       = True
  EEval t1 e1 == EEval t2 e2 = fromSing t1 == fromSing t2 && erase e1 == erase e2
  _           == _           = False

getDom :: forall (a :: Type TyPrim) (b :: Type TyPrim). (SingI a, SingI b)
    => CCore (a ':-> b) -> CType
getDom _ = fromSing (sing :: Sing a)

getCod :: forall (a :: Type TyPrim) (b :: Type TyPrim). (SingI a, SingI b)
    => CCore (a ':-> b) -> CType
getCod _ = fromSing (sing :: Sing b)

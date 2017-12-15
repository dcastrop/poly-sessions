-- Wrapper on top of Language.Poly + C-like expressions
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Language.Poly.C
( PrimTy (..)
, C
, CInt
, CFloat
, CNum
, CType
, CExpr (..)
, CCore (..)
, module X
) where

import Language.Poly as X

-- Primitive functions and operations
data PrimTy = Int32 | Float32 | Vector Int PrimTy

type family C (a :: PrimTy) :: Type PrimTy where
  C a = 'TPrim a

type CInt   = C 'Int32
type CFloat = C 'Float32

class CNum (a :: PrimTy) where
instance CNum 'Int32 where
instance CNum 'Float32 where

type CType = Type PrimTy

data CExpr (t :: Type PrimTy) where
    Plus  :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Minus :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Mult  :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Div   :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Mod   :: CNum a => CExpr (C a ':-> C a ':-> C a)
    Get   :: CExpr (C ('Vector i a) ':-> CInt ':-> C a)
    Put   :: CExpr (CInt ':-> C a ':-> C ('Vector i a) ':-> C ('Vector i a))

data CCore = forall e. CCore { unCore :: Core CExpr e }

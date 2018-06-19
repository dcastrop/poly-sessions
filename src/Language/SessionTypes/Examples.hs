{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Language.SessionTypes.Examples
where

import Prelude hiding ( (.), id, const, fst, snd, uncurry )
import Control.Constrained.Arrow
import Control.Constrained.Category
import Control.Constrained.ArrowVector
import Control.Constrained.ArrowFunctor
import Data.Typeable
import Data.Singletons
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.Num
import Data.Type.Mod
import Data.Type.Vector ( Vec )
import Data.Text.Prettyprint.Doc ( pretty )
import GHC.Exts ( Constraint )

import Language.Poly
import Language.SessionTypes.TSession.Syntax

testGenR :: (Typeable a, Typeable b) => a :=> b -> IO ()
testGenR g = print $ pretty $ generateR g

testGen :: (Typeable a, Typeable b) => r ::: a -> a :=> b -> IO ()
testGen ri g = print $ pretty $ generate ri g

iter :: Int -> (a -> a -> a) -> a -> a -> a
iter i c idf f = go i
  where
    go j | j <= 0     = idf
         | j == 1     = f
         | otherwise = f `c` go (j-1)

example1 :: Int :=> Int
example1 = id

inc :: Int :-> Int
inc = add . (id &&& const 1)
  where
    add :: (Int, Int) :-> Int
    add = arr "(+)" (uncurry (+))

example2 :: Int :=> Int
example2 = example1 . wrap inc . example1

example3 :: Int :=> (Int, Int)
example3 = gSplit (wrap inc) id

ex1 :: SPoly ('PProd 'PId 'PId)
ex1 = FProd FId FId

example4 :: (Int, Int) :=> (Int, Int)
example4 = pmap ex1 (wrap inc)

example5 :: (Int, Int) :=> (Int, Int)
example5 = snd &&& fst

example51 :: (Int, Int) :=> (Int, Int)
example51 = example5 . example5 . example5

example52 :: (Int, Int) :=> (Int, Int)
example52 = example5 . example5

double :: Int :-> Int
double = mult . (id &&& const 2)
  where
    mult :: (Int, Int) :-> Int
    mult =  arr "(*)" (uncurry (*))


example6 :: Either Int Int :=> Int
example6 = gCase (wrap inc) (wrap double)

example7 :: Either Int Int :=> Int
example7 = gCase (wrap double) (wrap inc) . gCase (inr . wrap inc) (inl . wrap double)

example71 :: (Either Int Int, Either Int Int) :=> Int
example71 = go . ((wrap inc ||| wrap double) *** (wrap double ||| wrap inc))
  where
    go :: (Int, Int) :=> Int
    go = arr "(+)" (uncurry (+))

example8 :: Either Int Int :=> Either Int Int
example8 = gCase gInr gInl

example9 :: (Int, Int) :=> (Int, Int)
example9 = gSplit (wrap inc) id . gFst

-- RING with products
-- Poly Level
-- type family V3 :: Poly Type where
--   V3 = 'PProd 'PId ('PProd 'PId 'PId)
--
-- split3 :: (ArrowChoice t, C t a, C t b, C t (b, b))
--        => t a b
--        -> t a b
--        -> t a b
--        -> t a (V3 :@: b)
-- split3 f g h = f &&& (g &&& h)
--
-- prj1 :: (ArrowChoice t, C t a, C t (a,a))
--      => t (V3 :@: a) a
-- prj1 = fst
--
-- prj2 :: (ArrowChoice t, C t a, C t (a,a), C t (a, (a,a)))
--      => t (V3 :@: a) a
-- prj2 = fst . snd
--
-- prj3 :: (ArrowChoice t, C t a, C t (a,a), C t (a,  (a,a)))
--      => t (V3 :@: a) a
-- prj3 = snd . snd
--
-- permute :: ( ArrowChoice t, C t a, C t b, C t (a, b)
--            , C t ((a,b),(a,b)), C t (V3 :@: (a,b)))
--         => t (V3 :@: (a, b)) (V3 :@: (a, b))
-- permute = split3 ((fst . prj1) &&& (snd . prj3))
--                  ((fst . prj2) &&& (snd . prj1))
--                  ((fst . prj3) &&& (snd . prj2))
--
-- ring :: ( ArrowChoice t, C t a, C t b
--            , C t (a, b), C t ((a, b), (a, b)), C t (a, a)
--            , C t (a, (a, a))
--            , C t ((a, b), ((a, b), (a, b))) )
--         => t a b
--         -> t (a, b) a
--         -> t (V3 :@: a) (V3 :@: a)
-- ring f g =
--     pmap (sing :: Sing V3) fst .
--     iter 2 (.) id (pmap (sing :: Sing V3) (g &&& snd) . permute) .
--     pmap (sing :: Sing V3) (id &&& f)
--
-- ex1Proto :: (V3 :@: Int) :=> (V3 :@: Int)
-- ex1Proto = ring id (arr "(+)" (uncurry (+)))
--
-- genV3 :: IO ()
-- genV3 = testGen
--     (RP (RI PType SZ) (RP (RI PType (SS SZ)) (RI PType (SS (SS SZ)))))
--     ex1Proto

-- RING with products
-- Poly Level

type SessionC t = (ArrowVector Typeable Vec t, ArrowChoice Typeable t)

permute :: forall n t a b. ( SessionC t, Typeable b, Typeable a, KnownNat n)
        => t (Vec n (a, b)) (Vec n (a, b))
permute = vec (\l -> (fst . proj l) &&& (snd . proj (l + 1)))

permute2 :: ( SessionC t, Typeable a, KnownNat n)
        => t (Vec n a) (Vec n (a,a))
permute2 = vec (\l -> proj l &&& proj (l + 1))

ring :: ( SessionC t, Typeable a, Typeable b, KnownNat n )
        => Int -> (a -> b) -> ((a,b) -> a) -> t (Vec n a) (Vec n a)
ring i f g =
    amap fst .
    iter i (.) id ((amap $ arr "g" (g &&& snd)) . permute) .
    amap (arr "f" (id &&& f))

ringExample :: forall n. KnownNat n => (Vec n Int) :=> (Vec n Int)
ringExample = ring (fromIntegral $ natVal (sing :: SNat n)) id (uncurry (+))

-- Butterfly

evensOdds :: forall n t a. ( SessionC t, Typeable a, KnownNat n)
         =>  t (Vec (2 * n) a) (Vec n a, Vec n a)
evensOdds =
  withKnownNat ((sing :: SNat 2) %* (sing :: SNat n)) $
  vec (\l -> proj (extMod @n @2 0 l)) &&& vec (\l -> proj (extMod @n @2 1 l))

splitVec :: forall n m t a. (SessionC t, KnownNat n, KnownNat m, Typeable a)
         =>  t (Vec (n + m) a) (Vec n a, Vec m a)
splitVec =
  vec (\l -> proj (weakenMod @m l)) &&& vec (\l -> proj (weakenMod @n l))

zipVec :: forall n t a b. ( SessionC t, Typeable a, Typeable b, KnownNat n )
       => t (Vec n a, Vec n b) (Vec n (a,b))
zipVec = vec (\l -> (proj l . fst) &&& (proj l . snd))

zipWithV :: forall n t a b c. ( SessionC t, Typeable a, Typeable b, Typeable c
                        , KnownNat n)
       => t (a,b) c -> t (Vec n a, Vec n b) (Vec n c)
zipWithV f = amap f . zipVec

append :: forall n m t a. ( SessionC t, Typeable a, KnownNat n, KnownNat m )
       => t (Vec n a, Vec m a) (Vec (n+m) a)
append = withKnownNat nm $
  vec (\l -> case splitMod l of
              Left l' -> proj l' . fst
              Right r' -> proj r' . snd)
  where
    nm = (sing :: SNat n) %+ (sing :: SNat m)

data INat where
  Z :: INat
  S :: INat -> INat

data RNat n where
  SZ :: RNat 'Z
  SS :: RNat r -> RNat ('S r)

type family ToNat (i :: INat) :: Nat where
  ToNat 'Z = 0
  ToNat ('S n) = 1 + ToNat n

type family FromNat (i :: Nat) :: INat where
  FromNat 0 = 'Z
  FromNat n = 'S (FromNat (n-1))

type family Pred (i :: INat) :: INat where
  Pred ('S n) = n
  Pred 'Z = 'Z

data SomeNat = forall n. SomeNat (RNat n)

type family MkCnstr (n :: INat) k a b :: Constraint where
  MkCnstr n k a b = (k a, k b, k (Vec (2 ^ (ToNat n)) a), k (Vec (2 ^ (ToNat n)) b))

class RecNat n where
  recNat :: RNat n

instance RecNat 'Z where
  recNat = SZ
instance RecNat n => RecNat ('S n) where
  recNat = SS recNat

butterflyR :: forall n t a b. ( SessionC t, Typeable a, Typeable b, KnownNat (ToNat n) )
           => RNat n -> t a b -> t (b,b) b -> t (Vec (2 ^ (ToNat n)) a) (Vec (2 ^ (ToNat n)) b)
butterflyR SZ f _ = amap f
butterflyR (SS n) f g =
  append . ((zipWithV g &&& (zipWithV g . (snd &&& fst))) . (butterflyR n f g *** butterflyR n f g)) . evensOdds

butterfly :: forall n t a b. ( SessionC t, Typeable a, Typeable b, RecNat (FromNat n), KnownNat n, ToNat (FromNat n) ~ n)
           => t a b -> t (b,b) b -> t (Vec (2 ^ n) a) (Vec (2 ^ n) b)
butterfly f g = butterflyR (recNat :: RNat (FromNat n)) f g

butterflyExample :: forall n. (KnownNat n, RecNat (FromNat n), ToNat (FromNat n) ~ n) => (Vec (2^n) Int) :=> (Vec (2^n) Int)
butterflyExample = butterfly id (wrap $ arr "(*)" (uncurry (*))) . vec (\l -> wrap (proj l))

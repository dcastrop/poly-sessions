{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Data.Singletons.Prelude.Bool
import Data.Singletons.Prelude.Eq
import Data.Type.Mod
import Data.Type.Vector ( Vec )
import Data.Text.Prettyprint.Doc ( pretty )

import Unsafe.Coerce

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
-- ex1Poly :: ( ArrowChoice t, C t a, C t b
--            , C t (a, b), C t ((a, b), (a, b)), C t (a, a)
--            , C t (a, (a, a))
--            , C t ((a, b), ((a, b), (a, b))) )
--         => t a b
--         -> t (a, b) a
--         -> t (V3 :@: a) (V3 :@: a)
-- ex1Poly f g =
--     pmap (sing :: Sing V3) fst .
--     iter 2 (.) id (pmap (sing :: Sing V3) (g &&& snd) . permute) .
--     pmap (sing :: Sing V3) (id &&& f)
--
-- ex1Proto :: (V3 :@: Int) :=> (V3 :@: Int)
-- ex1Proto = ex1Poly id (arr "(+)" (uncurry (+)))
--
-- genV3 :: IO ()
-- genV3 = testGen
--     (RP (RI PType SZ) (RP (RI PType (SS SZ)) (RI PType (SS (SS SZ)))))
--     ex1Proto

-- RING with products
-- Poly Level

permute :: ( ArrowVector t, ArrowChoice t, C t a, C t b
          , C t (a, b), KnownNat n, C t n, C t (Vec n (a, b)), Num (TMod n))
        => SNat n -> t (Vec n (a, b)) (Vec n (a, b))
permute n = vec n (\l -> (fst . proj l) &&& (snd . proj (l + 1)))

permute2 :: ( ArrowVector t, ArrowChoice t, C t (a,a), C t (Vec n a), KnownNat n, C t a, Num (TMod n) )
        => SNat n -> t (Vec n a) (Vec n (a,a))
permute2 n = vec n (\l -> proj l &&& proj (l + 1))

ex1Poly :: ( ArrowVector t, ArrowChoice t, C t a, C t (Vec n a), C t (Vec n (a,b))
          , C t (a,b), C t b, C t (SNat n), C t n, KnownNat n, Num (TMod n))
        => Int
        -> SNat n
        -> (a -> b)
        -> ((a,b) -> a)
        -> t (Vec n a) (Vec n a)

ex1Poly i n f g =
    amap fst .
    iter i (.) id ((amap $ arr "g" (g &&& snd))  . permute n) .
    amap (arr "f" (id &&& f))

ex1Proto :: forall n. (Typeable n, KnownNat n, Num (TMod n)) => (Vec n Int) :=> (Vec n Int)
ex1Proto = ex1Poly 3 (sing :: SNat n) id (uncurry (+))

-- genV :: IO ()
-- genV = testGen
--     (RVS (RI PType SZ) (RVS (RI PType (SS SZ)) (RVS (RI PType (SS (SS SZ))) (RVS (RI PType (SS (SS (SS SZ)))) RVZ))))
--     ex1Proto

-- Butterfly

evensOdds :: forall n t a. (KnownNat n, ArrowVector t
                      , C t a, C t (Vec (2 * n) a), C t (Vec n a) )
         =>  t (Vec (2 * n) a) (Vec n a, Vec n a)
evensOdds =
  vec n (\l -> proj (extMod 0 l)) &&& vec n (\l -> proj (extMod 1 l))
  where
    n = sing :: SNat n

splitVec :: forall n m t a. (KnownNat n, KnownNat m, ArrowVector t
                      , C t a, C t (Vec (m + n) a), C t (Vec n a), C t (Vec m a))
         =>  t (Vec (n + m) a) (Vec n a, Vec m a)
splitVec =
  vec n (\l -> proj (weakenMod @m l)) &&& vec m (\l -> proj (weakenMod @n l))
  where
    n = sing :: SNat n
    m = sing :: SNat m

zipVec :: forall n t a b. (KnownNat n, C t a, C t b, C t (Vec n a), C t (Vec n b),
                     C t (a,b), C t (Vec n a, Vec n b), C t (Vec n (a,b)),
                     ArrowVector t)
       => t (Vec n a, Vec n b) (Vec n (a,b))
zipVec = vec (sing :: SNat n) (\l -> (proj l . fst) &&& (proj l . snd))

zipWithV :: forall n t a b c. (KnownNat n, C t a, C t b, C t (Vec n a), C t (Vec n b),
                     C t (a,b), C t (Vec n a, Vec n b), C t (Vec n (a,b)),
                     C t (Vec n c), C t c, ArrowVector t)
       => t (a,b) c -> t (Vec n a, Vec n b) (Vec n c)
zipWithV f = amap f . zipVec

append :: forall n m t a. (KnownNat n, KnownNat m, ArrowVector t,
                    C t a, C t (Vec n a), C t (Vec m a), C t (Vec n a, Vec m a)
                    , C t (Vec (n+m) a))
       => t (Vec n a, Vec m a) (Vec (n+m) a)
append = withKnownNat nm $
         vec nm (\l -> case splitMod l of
                        Left l' -> proj l' . fst
                        Right r' -> proj r' . snd)
  where
    nm = n %+ m
    n = sing :: SNat n
    m = sing :: SNat m


data IfNat n where
  IfZero :: n ~ 0 => IfNat n
  IfSucc :: n ~ (m + 1) => SNat m -> IfNat n

nIf :: forall a (c :: Bool). Sing c -> a -> a -> a
nIf STrue x _ = x
nIf SFalse _ y = y

ifZero :: SNat n -> IfNat n
ifZero n = nIf (n %== (sing :: SNat 0)) (unsafeCoerce IfZero)
           (unsafeCoerce (IfSucc m))
  where
    m = n %- (sing :: SNat 1)


split :: forall n t a. (KnownNat n, ArrowVector t, C t a
                 , C t (Vec ((2 ^ n) + (2 ^ n)) a), C t (Vec (2 ^ n) a),
                 C t (Vec ((2 ^ (n - 1)) + (2 ^ (n - 1))) a),
                         C t (Vec (2 ^ (n - 1)) a))
      => Either (t (Vec (2^n) a) (Vec (2^n) a)) (t (Vec (2^n) a) (Vec (2^(n-1)) a, Vec (2^(n-1)) a))
split = case ifZero n of
          IfZero -> Left id
          IfSucc _ -> Right splitVec

  where
    n = sing :: SNat n

butterfly :: forall n t a b. ( KnownNat n, C t a, C t b, ArrowVector t , C t a,
                       C t (Vec (2^n) a), C t (Vec (2^n) b), C t (b, b))
          => t a b -> t (b,b) b -> t (Vec (2 ^ n) a) (Vec (2 ^ n) b)
butterfly f g =
  case ifZero n of
    IfZero -> amap f
    IfSucc (m :: SNat x) ->
      case natDict @t ((sing :: SNat 2) %^ m) of
        CDict -> case natDict @t (((sing :: SNat 2) %^ m) %+ ((sing :: SNat 2) %^ m)) of
         CDict -> case natDict @t ((sing :: SNat 2) %* (sing :: SNat 2) %^ m) of
          CDict -> case (vecDict @t @a @(2 ^ x), vecDict @t @b @(2 ^ x), vecDict @t @(b,b) @(2 ^ x)) of
           (CDict, CDict, CDict) -> case (vecDict @t @a @((2 ^ x) + (2 ^ x)), vecDict @t @b @((2 ^ x) + (2 ^ x))) of
             (CDict, CDict) -> case (pairDict @t @(Vec (2^x) a) @(Vec (2^x) a), pairDict @t @(Vec (2^x) b) @(Vec (2^x) b)) of
               (CDict, CDict) -> case vecDict @t @a @(2 * (2 ^ x)) of
                  CDict
                    -> append . ((zipWithV g &&& (zipWithV g . (snd &&& fst))) . (butterfly f g *** butterfly f g)) . evensOdds
  where
    n = sing :: SNat n


ex2Proto :: forall n. (Typeable (2^n), KnownNat n, Num (TMod n)) => (Vec (2^n) Int) :=> (Vec (2^n) Int)
ex2Proto = butterfly @n id (wrap $ arr "(*)" (uncurry (*))) . vec (sing :: SNat (2^n)) (\l -> wrap (proj l))

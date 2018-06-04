{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.SessionTypes.Examples
where

import Prelude hiding ( (.), id, const, fst, snd )
import Control.Constrained.Arrow
import Control.Constrained.Category
import Data.Kind
import Data.Typeable
import Data.Type.Natural
import Data.Singletons
import Data.Text.Prettyprint.Doc ( pretty )

import Language.FPoly
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
inc = add . one
  where
    add :: (Int, Int) :-> Int
    add = arr "(+)" (uncurry (+))
    one :: Int :-> (Int, Int)
    one = id &&& const 1

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
double = mult . two
  where
    mult :: (Int, Int) :-> Int
    mult =  arr "(*)" (uncurry (*))
    two :: Int :-> (Int, Int)
    two = id &&& const 2

example6 :: Either Int Int :=> Int
example6 = gCase (wrap inc) (wrap double)

example7 :: Either Int Int :=> Int
example7 = gCase (wrap double) (wrap inc) . gCase (inr . wrap inc) (inl . wrap double)

-- example71 :: (Either Int Int, Either Int Int) :=> (Int, Int)
example71 = go . ((wrap inc ||| wrap double) *** (wrap double ||| wrap inc))
  where
    go :: (Int, Int) :=> Int
    go = arr "(+)" (uncurry (+))

example8 :: Either Int Int :=> Either Int Int
example8 = gCase gInr gInl

example9 :: (Int, Int) :=> (Int, Int)
example9 = gSplit (wrap inc) id . gFst

-- RING
-- Poly Level
type family V3 :: Poly Type where
  V3 = 'PProd 'PId ('PProd 'PId 'PId)

split3 :: (ArrowChoice t, C t a, C t b, C t (b, b))
       => t a b
       -> t a b
       -> t a b
       -> t a (V3 :@: b)
split3 f g h = f &&& (g &&& h)

prj1 :: (ArrowChoice t, C t a, C t (a,a))
     => t (V3 :@: a) a
prj1 = fst

prj2 :: (ArrowChoice t, C t a, C t (a,a), C t (a, (a,a)))
     => t (V3 :@: a) a
prj2 = fst . snd

prj3 :: (ArrowChoice t, C t a, C t (a,a), C t (a,  (a,a)))
     => t (V3 :@: a) a
prj3 = snd . snd

permute :: ( ArrowChoice t, C t a, C t b, C t (a, b)
           , C t ((a,b),(a,b)), C t (V3 :@: (a,b)))
        => t (V3 :@: (a, b)) (V3 :@: (a, b))
permute = split3 ((fst . prj1) &&& (snd . prj3))
                 ((fst . prj2) &&& (snd . prj1))
                 ((fst . prj3) &&& (snd . prj2))

ex1Poly :: ( ArrowChoice t, C t a, C t b
           , C t (a, b), C t ((a, b), (a, b)), C t (a, a)
           , C t (a, (a, a))
           , C t ((a, b), ((a, b), (a, b))) )
        => t a b
        -> t (a, b) a
        -> t (V3 :@: a) (V3 :@: a)
ex1Poly f g =
    pmap (sing :: Sing V3) fst .
    iter 2 (.) id (pmap (sing :: Sing V3) (g &&& snd) . permute) .
    pmap (sing :: Sing V3) (id &&& f)

ex1Proto :: (V3 :@: Int) :=> (V3 :@: Int)
ex1Proto = ex1Poly id (arr "(+)" (uncurry (+)))

genV3 :: IO ()
genV3 = testGen
    (RP (RI PType SZ) (RP (RI PType (SS SZ)) (RI PType (SS (SS SZ)))))
    ex1Proto

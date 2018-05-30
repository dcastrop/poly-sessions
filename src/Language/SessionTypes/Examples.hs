{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.SessionTypes.Examples
where

import Prelude hiding ( (.), id, const, fst, snd )
import Control.Constrained.Arrow
import Control.Constrained.Category
import Data.Typeable
import Data.Text.Prettyprint.Doc ( pretty )

import Language.FPoly
import Language.SessionTypes.TSession.Syntax

testGen :: (Typeable a, Typeable b) => a :=> b -> IO ()
testGen g = putStrLn $ show $ pretty $ generate g

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
example2 = example1 . lift inc . example1

example3 :: Int :=> (Int, Int)
example3 = gSplit (lift inc) id

ex1 :: SPoly ('PProd 'PId 'PId)
ex1 = FProd FId FId

example4 :: (Int, Int) :=> (Int, Int)
example4 = gfmap ex1 (lift inc)

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
example6 = gCase (lift inc) (lift double)

example7 :: Either Int Int :=> Int
example7 = gCase (lift inc) (lift inc) . gCase (gInl . lift inc) (gInr . lift double)

example8 :: Either Int Int :=> Either Int Int
example8 = gCase gInl gInr

example9 :: (Int, Int) :=> (Int, Int)
example9 = gSplit id id . gFst
--
--
-- -- RING
-- -- Poly Level
-- type V3 = 'PProd 'PId ('PProd 'PId 'PId)
--
-- split3 :: (SingI a, SingI b)
--        => CCore (a ':-> b)
--        -> CCore (a ':-> b)
--        -> CCore (a ':-> b)
--        -> CCore (a ':-> V3 :@: b)
-- split3 f g h = Split f (Split g h)
--
-- prj1 :: SingI a => CCore (V3 :@: a ':-> a)
-- prj1 = Fst
--
-- prj2 :: SingI a => CCore (V3 :@: a ':-> a)
-- prj2 = Fst `Comp` Snd
--
-- prj3 :: SingI a => CCore (V3 :@: a ':-> a)
-- prj3 = Snd `Comp` Snd
--
-- permute :: (SingI a, SingI b)
--         => CCore ((V3 :@: 'TProd a b) ':-> (V3 :@: 'TProd a b))
-- permute = split3 (Split (Fst `Comp` prj1) (Snd `Comp` prj3))
--                  (Split (Fst `Comp` prj2) (Snd `Comp` prj1))
--                  (Split (Fst `Comp` prj3) (Snd `Comp` prj2))
--
-- ex1Poly :: forall (a :: Type TyPrim) b. (SingI a, SingI b)
--         => CCore (a ':-> b)
--         -> CCore ('TProd a b ':-> a)
--         -> CCore (V3 :@: a ':-> V3 :@: a)
-- ex1Poly f g =
--     Fmap (sing :: Sing V3) Fst `Comp`
--     iter 2 Comp Id (Fmap (sing :: Sing V3) (Split g Snd) `Comp` permute) `Comp`
--     Fmap (sing :: Sing V3) (Split Id f)
--
-- -- Session Level
--
-- gsplit3 :: (SingI a, SingI b)
--         => a :=> b -> a :=> b -> a :=> b -> a :=> (V3 :@: b)
-- gsplit3 f g h = gsplit f (gsplit g h)
--
-- gpermute :: (SingI a, SingI b)
--         => ((V3 :@: 'TProd a b) :=> (V3 :@: 'TProd a b))
-- gpermute =
--     gsplit3 (gsplit (lift Fst `gcomp` lift prj1) (lift Snd `gcomp` lift prj3))
--             (gsplit (lift Fst `gcomp` lift prj2) (lift Snd `gcomp` lift prj1))
--             (gsplit (lift Fst `gcomp` lift prj3) (lift Snd `gcomp` lift prj2))
--
-- ex1Session :: forall (a :: Type TyPrim) b. (SingI a, SingI b)
--         => CCore (a ':-> b)
--         -> CCore ('TProd a b ':-> a)
--         -> (V3 :@: a) :=> (V3 :@: a)
-- ex1Session f g =
--     gfmap (sing :: Sing V3) (lift Fst) `gcomp`
--     iter 2 gcomp (lift Id)
--       (gfmap (sing :: Sing V3)
--              (gsplit (lift g) (lift Snd))
--        `gcomp` gpermute) `gcomp`
--     -- lift (Fmap (sing :: Sing V3) (Split Id f))
--     gfmap (sing :: Sing V3) (gsplit (lift Id) (lift f))
--
-- ex1Proto :: (V3 :@: CInt) :=> (V3 :@: CInt)
-- ex1Proto = ex1Session Id (Prim Plus)

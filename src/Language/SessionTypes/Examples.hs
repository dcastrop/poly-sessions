{-# LANGUAGE TypeInType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.SessionTypes.Examples
where

import Data.Singletons
import Data.Text.Prettyprint.Doc ( Pretty, pretty )
import Data.Text.Prettyprint.EDoc

import Language.Poly.C
import Language.SessionTypes.Common
import Language.SessionTypes.Combinators
import Language.SessionTypes.RwSession

iter :: Int -> (a -> a -> a) -> a -> a -> a
iter i comp idf f
  | i <= 0     = idf
  | i == 1     = f
  | otherwise = f `comp` iter (i-1) comp idf f



exgen1 :: CInt :=> CInt
exgen1 = lift (Id :: CCore (CInt ':-> CInt))

example1 :: Proto
example1 = getGen exgen1 (Rol 0) (Rol 1)

inc :: CCore (CInt ':-> CInt)
inc = Prim Plus `Comp` Split Id (Const $ Prim $ CInt 1)

exgen2 :: CInt :=> CInt
exgen2 = lift inc `gcomp` exgen1

example2 :: Proto
example2 = getGen exgen2 (Rol 0) (Rol 1)

exrw21 :: Maybe Proto
exrw21 = rwL strat example2
  where
    strat = IdL

exrw22 :: [(Equiv, Proto)]
exrw22 = simpl example2

exgen3 :: CInt :=> 'TProd CInt CInt
exgen3 = gsplit (lift inc) (lift Id)

example3 :: Proto
example3 = getGen exgen3 (Rol 0) (Rol 1)


-- RING
-- Poly Level
type V3 = 'PProd 'PId ('PProd 'PId 'PId)

split3 :: (SingI a, SingI b)
       => CCore (a ':-> b)
       -> CCore (a ':-> b)
       -> CCore (a ':-> b)
       -> CCore (a ':-> V3 :@: b)
split3 f g h = Split f (Split g h)

prj1 :: SingI a => CCore (V3 :@: a ':-> a)
prj1 = Fst

prj2 :: SingI a => CCore (V3 :@: a ':-> a)
prj2 = Fst `Comp` Snd

prj3 :: SingI a => CCore (V3 :@: a ':-> a)
prj3 = Snd `Comp` Snd

permute :: (SingI a, SingI b)
        => CCore ((V3 :@: 'TProd a b) ':-> (V3 :@: 'TProd a b))
permute = split3 (Split (Fst `Comp` prj1) (Snd `Comp` prj3))
                 (Split (Fst `Comp` prj2) (Snd `Comp` prj1))
                 (Split (Fst `Comp` prj3) (Snd `Comp` prj2))

ex1Poly :: forall (a :: Type TyPrim) b. (SingI a, SingI b)
        => CCore (a ':-> b)
        -> CCore ('TProd a b ':-> a)
        -> CCore (V3 :@: a ':-> V3 :@: a)
ex1Poly f g =
    Fmap (sing :: Sing V3) Fst `Comp`
    iter 2 Comp Id (Fmap (sing :: Sing V3) (Split g Snd) `Comp` permute) `Comp`
    Fmap (sing :: Sing V3) (Split Id f)

-- Session Level

gsplit3 :: (SingI a, SingI b)
        => a :=> b -> a :=> b -> a :=> b -> a :=> (V3 :@: b)
gsplit3 f g h = gsplit f (gsplit g h)

gpermute :: (SingI a, SingI b)
        => ((V3 :@: 'TProd a b) :=> (V3 :@: 'TProd a b))
gpermute =
    gsplit3 (gsplit (lift Fst `gcomp` lift prj1) (lift Snd `gcomp` lift prj3))
            (gsplit (lift Fst `gcomp` lift prj2) (lift Snd `gcomp` lift prj1))
            (gsplit (lift Fst `gcomp` lift prj3) (lift Snd `gcomp` lift prj2))

ex1Session :: forall (a :: Type TyPrim) b. (SingI a, SingI b)
        => CCore (a ':-> b)
        -> CCore ('TProd a b ':-> a)
        -> (V3 :@: a) :=> (V3 :@: a)
ex1Session f g =
    gfmap (sing :: Sing V3) (lift Fst) `gcomp`
    iter 2 gcomp (lift Id)
      (gfmap (sing :: Sing V3)
             (gsplit (lift g) (lift Snd))
       `gcomp` gpermute) `gcomp`
    gfmap (sing :: Sing V3) (gsplit (lift Id) (lift f))

ex1Proto :: Proto
ex1Proto = getGen (ex1Session Id intPlus) (Rol 0) (Rol 1)
  where
    intPlus :: CCore ('TProd CInt CInt ':-> CInt)
    intPlus = Prim Plus

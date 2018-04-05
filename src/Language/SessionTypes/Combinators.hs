{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Language.SessionTypes.Combinators
  ( Proto
  , (:=>)(..)
  , lift
  , gcomp
  , gsplit
  , gprod
  , gsum
  , gcase
  , gfmap
  ) where

import Data.Singletons ( SingI (..), fromSing )
import Data.Set ( Set )
import qualified Data.Set as Set

import Language.Poly.C
import Language.SessionTypes.Common
import Language.SessionTypes.Prefix.Global

type Proto = GT CType ECore

newtype (:=>) (a :: Type TyPrim) (b :: Type TyPrim)
  = ParGen { getGen :: Role -> Role -> Proto }

lift :: forall a b. (SingI a, SingI b)
     => CCore (a ':-> b) -> a :=> b
lift x = ParGen $ \ri ro ->
  Comm (Msg [ri] [ro] (getDom x) (EEval sing x))

liftS :: forall a b. Sing a -> Sing b
     -> CCore (a ':-> b) -> a :=> b
liftS s1 s2 x = ParGen $ \ri ro ->
  Comm (Msg [ri] [ro] (fromSing s1) (EEval (STArr s1 s2) x))

gen :: Set Role -> Role
gen rs = Rol $ head [ r | r <- [(0::Int)..], Rol r `Set.notMember` rs]

gcomp :: forall a b c. (SingI a, SingI b, SingI c)
     => b :=> c -> a :=> b -> a :=> c
gcomp g2 g1 = ParGen $
  \ri ro ->
    let rt = gen (fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro))
    in NewRole rt $ getGen g1 ri rt `gSeq` getGen g2 rt ro

gcompS :: forall a b c. b :=> c -> a :=> b -> a :=> c
gcompS g2 g1 = ParGen $
  \ri ro ->
    let rt = gen (fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro))
    in NewRole rt $ getGen g1 ri rt `gSeq` getGen g2 rt ro

gsplit :: forall a b c. (SingI a, SingI b, SingI c)
      => a :=> b -> a :=> c -> a :=> ('TProd b c)
gsplit = gsplitS sing sing

gsplitS :: forall a b c. Sing b -> Sing c
      -> a :=> b -> a :=> c -> a :=> ('TProd b c)
gsplitS b c g1 g2 = ParGen $
  \ri ro ->
    let rs = fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro)
        rt1 = gen rs
        rt2 = gen $ Set.insert rt1 rs
    in NewRole rt1 $ NewRole rt2 $
       (getGen g1 ri rt1 `gPar` getGen g2 ri rt2)
       `gSeq` Comm (Msg [rt1,rt2] [ro]
                    (fromSing (STProd b c))
                    (EEval (STArr (STProd b c) (STProd b c)) Id))

gprod :: forall a1 a2 b1 b2. (SingI a1, SingI a2, SingI b1, SingI b2)
      => a1 :=> b1 -> a2 :=> b2
      -> ('TProd a1 a2) :=> ('TProd b1 b2)
gprod g1 g2 =
  gsplit (g1 `gcomp` lift Fst) (g2 `gcomp` lift Snd)

gprodS :: forall a1 a2 b1 b2. Sing a1 -> Sing a2 -> Sing b1 -> Sing b2
      -> a1 :=> b1 -> a2 :=> b2
      -> ('TProd a1 a2) :=> ('TProd b1 b2)
gprodS a1 a2 b1 b2 g1 g2 =
  gsplitS b1 b2
  (g1 `gcompS` liftS (STProd a1 a2) a1 Fst)
  (g2 `gcompS` liftS (STProd a1 a2) a2 Snd)


gcase :: forall a b c. (SingI a, SingI b, SingI c)
      => (a :=> c) -> b :=> c -> ('TSum a b) :=> c
gcase g1 g2 = ParGen $
  \ri ro ->
    Choice ri (addAlt 0 EIdle (getGen g1 ri ro) $
                addAlt 1 EIdle (getGen g2 ri ro) emptyAlt)

gcaseS :: forall a b c.
       (a :=> c) -> b :=> c -> ('TSum a b) :=> c
gcaseS g1 g2 = ParGen $
  \ri ro ->
    Choice ri (addAlt 0 EIdle (getGen g1 ri ro) $
                addAlt 1 EIdle (getGen g2 ri ro) emptyAlt)


gsum :: forall a1 a2 b1 b2. (SingI b1, SingI b2)
       => (a1 :=> b1) -> a2 :=> b2 -> ('TSum a1 a2) :=> ('TSum b1 b2)
gsum = gsumS sing sing

gsumS :: forall a1 a2 b1 b2. Sing b1 -> Sing b2
      -> (a1 :=> b1) -> a2 :=> b2 -> ('TSum a1 a2) :=> ('TSum b1 b2)
gsumS b1 b2 g1 g2
  = gcaseS (liftS b1 (STSum b1 b2) Inl `gcompS` g1)
           (liftS b2 (STSum b1 b2) Inr `gcompS` g2)

gfmap :: forall a b f. (SingI a, SingI b)
      => Sing f
      -> a :=> b
      -> (f :@: a) :=> (f :@: b)
gfmap (SPK s) _ = ParGen $ \ri ro ->
  Comm (Msg [ri] [ro] (fromSing s) EIdle)
gfmap SPId  f = f
gfmap (SPProd p1 p2) f =
    gprodS (app p1 (sing :: Sing a)) (app p2 (sing :: Sing a))
           (app p1 (sing :: Sing b)) (app p2 (sing :: Sing b))
           (gfmap p1 f) (gfmap p2 f)
gfmap (SPSum p1 p2) f =
    gsumS (app p1 (sing :: Sing b))
          (app p2 (sing :: Sing b))
          (gfmap p1 f) (gfmap p2 f)

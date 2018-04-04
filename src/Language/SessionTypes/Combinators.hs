{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Language.SessionTypes.Combinators
  ( Proto
  , (:=>)(..)
  , lift
  , gcomp
  , gsplit
  , gcase
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

gen :: Set Role -> Role
gen rs = Rol $ head [ r | r <- [(0::Int)..], Rol r `Set.notMember` rs]

gcomp :: forall a b c. (SingI a, SingI b, SingI c)
     => b :=> c -> a :=> b -> a :=> c
gcomp g2 g1 = ParGen $
  \ri ro ->
    let rt = gen (fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro))
    in NewRole rt $ getGen g1 ri rt `gSeq` getGen g2 rt ro

gsplit :: forall a b c. (SingI a, SingI b, SingI c)
      => a :=> b -> a :=> c -> a :=> ('TProd b c)
gsplit g2 g1 = ParGen $
  \ri ro ->
    let rt1 = gen (fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro))
        rt2 = gen (fr (getGen g1 ri ro) `Set.union` fr (getGen g2 ri ro))
    in NewRole rt1 $ NewRole rt2 $
       (getGen g1 ri rt1 `gPar` getGen g2 ri rt2)
       `gSeq` Comm (Msg [rt1,rt2] [ro]
                    (fromSing (sing :: Sing ('TProd b c)))
                    (EEval (sing :: Sing ('TProd b c ':-> 'TProd b c)) Id))


gcase :: forall a b c. (SingI a, SingI b, SingI c)
      => (a :=> c) -> b :=> c -> ('TSum a b) :=> c
gcase g1 g2 = ParGen $
  \ri ro ->
    Choice ri (addAlt 0 EIdle (getGen g1 ri ro) $
                addAlt 1 EIdle (getGen g2 ri ro) emptyAlt)

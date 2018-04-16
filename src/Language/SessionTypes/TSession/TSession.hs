{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Language.SessionTypes.TSession
where

import Data.Kind hiding ( Type )

import Data.Singletons
import Data.Singletons.TypeLits

import Language.Poly.C
import Language.Poly.Core hiding ( Nat )
import Language.Poly.Type

data SRole :: * where
  SId :: Nat -> SRole
  SProd :: SRole -> SRole -> SRole
  SSum :: SRole -> SRole -> SRole

-- | Singletonized SRole.
data instance Sing (t :: SRole) where
  SI :: Sing n -> Sing ('SId n)
  SP :: Sing r1 -> Sing r2 -> Sing ('SProd r1 r2)
  SS :: Sing r1 -> Sing r2 -> Sing ('SSum r1 r2)

instance SingI n => SingI ('SId n) where
  sing = SI sing
instance (SingI a, SingI b) => SingI ('SProd a b) where
  sing = SP sing sing
instance (SingI a, SingI b) => SingI ('SSum a b) where
  sing = SS sing sing

-- | A 'role type' is either a sum of roles, product of roles, or a constant
data TRole :: * where
  RId :: Type TyPrim -> Nat -> TRole
  RProd :: TRole -> TRole -> TRole
  RSum :: TRole -> TRole -> TRole

type family (:::) (r :: SRole) (a :: Type TyPrim) = (s :: TRole) | s -> r a where
  (:::) ('SId n) t = 'RId t n
  (:::) ('SProd r1 r2) ('TProd a b) = 'RProd (r1 ::: a) (r2 ::: b)
  (:::) ('SSum r1 r2) ('TSum a b) = 'RSum (r1 ::: a) (r2 ::: b)

type family (:~:) (r :: SRole) (a :: Type TyPrim) = (s :: TRole) | s -> r a where
  (:~:) ('SId n) t = 'RId t n
  (:~:) ('SSum r1 r2) ('TSum a b) = 'RSum (r1 :~: a) (r2 :~: b)

-- | Singletonized role. Due to the use of Integers, I cannot derive these
-- using Data.Singletons.TH automatically
data instance Sing (t :: TRole) where
  RI :: Sing t -> Sing n -> Sing ('RId t n)
  RP :: Sing r1 -> Sing r2 -> Sing ('RProd r1 r2)
  RS :: Sing r1 -> Sing r2 -> Sing ('RSum r1 r2)

instance (SingI t, SingI n) => SingI ('RId t n) where
  sing = RI sing sing
instance (SingI a, SingI b) => SingI ('RProd a b) where
  sing = RP sing sing
instance (SingI a, SingI b) => SingI ('RSum a b) where
  sing = RS sing sing

type family EraseR (r :: TRole) :: Type TyPrim where
  EraseR ('RId t _) = t
  EraseR ('RProd a b) = 'TProd (EraseR a) (EraseR b)
  EraseR ('RSum a b) = 'TSum (EraseR a) (EraseR b)

data (:<:) :: TRole -> TRole -> * where
  LR :: r :<: r
  L1 :: r1 :<: r2 -> r1 :<: 'RProd r2 r3
  L2 :: r1 :<: r3 -> r1 :<: 'RProd r2 r3

data TPrefix :: TRole -> TRole -> * where
  TComm  :: Sing ri
         -> Sing ro
         -> CCore (EraseR ri ':-> EraseR ro)
         -> TPrefix ri ro

  TSplit  :: TPrefix ri ro1
          -> TPrefix ri ro2
          -> TPrefix ri ('RProd ro1 ro2)

  TSeq    :: Sing r
          -> TPrefix ri r
          -> TPrefix r  ro
          -> TPrefix ri ro

  TBranch :: TPrefix ri1 ro
          -> TPrefix ri2 ro
          -> TPrefix ('RSum ri1 ri2) ro

  TSkip   :: ro :<: ri
          -> TPrefix ri ro

lift :: forall r1 r2.
       (SingI r1, SingI r2)
     => CCore (EraseR r1 ':-> EraseR r2)
     -> TPrefix r1 r2
lift = TComm sing sing

-- distrib :: forall r1 r2 a b. (SingI r1, SingI r2)
--         => CCore (a ':-> b)
--         -> TPrefix (r1 :~: a) (r2 ::: b)
-- distrib = TCommS sing sing

gid :: forall r. TPrefix r r
gid = TSkip LR

gcomp :: forall r1 r2 r3. SingI r2 => TPrefix r2 r3 -> TPrefix r1 r2 -> TPrefix r1 r3
gcomp = flip $ TSeq sing

--- Products
gfst :: forall r1 r2. TPrefix ('RProd r1 r2) r1
gfst = TSkip (L1 LR)

gsnd :: forall r1 r2. TPrefix ('RProd r1 r2) r2
gsnd = TSkip (L2 LR)

gsplit :: forall r1 r2 r3. TPrefix r1 r2 -> TPrefix r1 r3
       -> TPrefix r1 ('RProd r2 r3)
gsplit = TSplit

gprod :: forall r1 r2 r3 r4. (SingI r1, SingI r2)
      => TPrefix r1 r3 -> TPrefix r2 r4
      -> TPrefix ('RProd r1 r2) ('RProd r3 r4)
gprod = gprodS sing sing

gprodS :: forall r1 r2 r3 r4. Sing r1 -> Sing r2
      -> TPrefix r1 r3 -> TPrefix r2 r4
      -> TPrefix ('RProd r1 r2) ('RProd r3 r4)
gprodS r1 r2 f g = gsplit (TSeq r1 gfst f)
                          (TSeq r2 gsnd g)

gcase :: forall r1 r2 r3. TPrefix r1 r3 -> TPrefix r2 r3
      -> TPrefix ('RSum r1 r2) r3
gcase = TBranch

-- Sums
ginl :: forall e1 e2. (SingI e1, SingI e2) => TPrefix e1 ('RSum e1 e2)
ginl = lift Inl

ginlS :: forall e1 e2. Sing e1 -> Sing e2 -> TPrefix e1 ('RSum e1 e2)
ginlS e1 e2 = TComm e1 (RS e1 e2) Inl

ginr :: forall e1 e2. (SingI e1, SingI e2) => TPrefix e2 ('RSum e1 e2)
ginr = lift Inr

ginrS :: forall e1 e2. Sing e1 -> Sing e2 -> TPrefix e2 ('RSum e1 e2)
ginrS e1 e2 = TComm e2 (RS e1 e2) Inr

gsum :: forall r1 r2 r3 r4.
       (SingI r3, SingI r4)
     => TPrefix r1 r3
     -> TPrefix r2 r4
     -> TPrefix ('RSum r1 r2) ('RSum r3 r4)
gsum f g = gcase (ginl `gcomp` f) (ginr `gcomp` g)

gsumS :: forall r1 r2 r3 r4.
       Sing r3
      -> Sing r4
      -> TPrefix r1 r3
      -> TPrefix r2 r4
      -> TPrefix ('RSum r1 r2) ('RSum r3 r4)
gsumS r3 r4 f g = gcase (TSeq r3 f $ ginlS r3 r4)
                        (TSeq r4 g $ ginrS r3 r4)

--- XXX: Functor refactor, combine with application in poly-lang
-- (maybe a typeclass?)
type RPoly = Poly TRole

type family (:@@:) (p :: RPoly) (t :: TRole) :: TRole where
  'PK c :@@: t = c
  'PId :@@: t = t
  'PProd p1 p2 :@@: t = 'RProd (p1 :@@: t) (p2 :@@: t)
  'PSum p1 p2 :@@: t = 'RSum (p1 :@@: t) (p2 :@@: t)

rapp :: forall (p :: RPoly) (t :: TRole).
       Sing p -> Sing t -> Sing (p :@@: t)
rapp SPId           t = t
rapp (SPK c)       _t = c
rapp (SPProd p1 p2) t = RP (p1 `rapp` t) (p2 `rapp` t)
rapp (SPSum p1 p2)  t = RS (p1 `rapp` t) (p2 `rapp` t)

gfmap :: forall r1 r2 f. (SingI r1, SingI r2)
      => Sing f
      -> TPrefix r1 r2
      -> TPrefix (f :@@: r1) (f :@@: r2)
gfmap (SPK _) _ = gid
gfmap SPId g = g
gfmap (SPProd p1 p2) f =
  gprodS (rapp p1 (sing :: Sing r1)) (rapp p2 (sing :: Sing r1))
         (gfmap p1 f) (gfmap p2 f)
gfmap (SPSum p1 p2) f =
  gsumS (rapp p1 (sing :: Sing r2)) (rapp p2 (sing :: Sing r2))
        (gfmap p1 f) (gfmap p2 f)

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
module Language.SessionTypes.TSession.Syntax
where

import Prelude hiding ( (.), id, fst, snd, const )

import Data.Kind

import Data.Singletons
import Data.Singletons.Decide
import Data.Type.Natural
import Data.Typeable
import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Constrained.Category
import Control.Constrained.Arrow
import Control.Monad.State.Strict hiding ( lift )
import Data.Text.Prettyprint.Doc ( Pretty(..) )

import Language.FPoly.Core
import Language.FPoly.Type
import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt )
import Language.SessionTypes.Prefix.Global

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.

data TId
  = TI Nat | TJ TId TRole
  deriving (Eq, Ord, Show)

data STId (k :: TId) where
  STI :: SNat n -> STId ('TI n)
  STJ :: STId n -> l ::: a -> STId ('TJ n l)

data TRole
  = RId TId
  | RProd TRole TRole
  | RSum  TRole TRole
  | RAny
  deriving (Eq, Ord, Show)

-- type family FstI (r :: TId) :: TId where
--   FstI ('TI n) = 'TI n
--   FstI ('TJ m r) = 'TJ (FstI m) (FstR r)

type family FstR (r :: TRole) :: TRole where
  FstR ('RId n) = 'RId n
  FstR ('RProd a _) = a
  FstR ('RSum a b) = 'RSum (FstR a) (FstR b)
  FstR 'RAny = 'RAny

-- type family SndI (r :: TId) :: TId where
--   SndI ('TI n) = 'TI n
--   SndI ('TJ m r) = 'TJ (SndI m) (SndR r)

type family SndR (r :: TRole) :: TRole where
  SndR ('RId n) = 'RId n
  SndR ('RProd _ b) = b
  SndR ('RSum a b) = 'RSum (SndR a) (SndR b)
  SndR 'RAny = 'RAny

type family EqN (l :: Nat) (r :: Nat) :: Bool where
  EqN 'Z 'Z = 'True
  EqN 'Z ('S m) = 'False
  EqN ('S n) 'Z = 'False
  EqN ('S n) ('S m) = EqN n m

type family And (b1 :: Bool) (b2 :: Bool) :: Bool where
  And 'False _ = 'False
  And _ 'False = 'False
  And 'True 'True = 'True

type family ITE (b :: Bool) (l :: k) (r :: k) = (res :: k) where
  ITE 'True l _ = l
  ITE 'False _ r = r

type family Unify (t1 :: TRole) (t2 :: TRole) :: TRole where
  Unify 'RAny r = r
  Unify r 'RAny  = r
  Unify ('RId n) ('RId m) = 'RId ('TJ n ('RId m))
  Unify ('RId n) ('RProd l r) = 'RId ('TJ n ('RProd l r))
  Unify ('RId n) ('RSum l r) = 'RId ('TJ n ('RSum l r))
  Unify ('RProd l r) ('RId n) = 'RId ('TJ n ('RProd l r))
  Unify ('RSum l r) ('RId n) = 'RId ('TJ n ('RSum l r))
  Unify ('RProd l1 r1) ('RProd l2 r2) = 'RProd (Unify l1 l2) (Unify r1 r2)
  Unify ('RSum l1 r1) ('RSum l2 r2) = 'RSum (Unify l1 l2) (Unify r1 r2)

infix 5 :::

data (:::) (t :: TRole) (a :: Type)  where
  RI :: PType t -> STId n -> 'RId n ::: t
  RP :: (Typeable a, Typeable b) => r1 ::: a -> r2 ::: b -> 'RProd r1 r2 ::: (a, b)
  RS :: Typeable a => r1 ::: a -> r2 ::: b -> 'RSum r1 r2  ::: Either a b
  RA :: Typeable a => 'RAny ::: a

unify :: r1 ::: a -> r2 ::: a -> Unify r1 r2 ::: a
unify RA x = x
unify x RA = x
unify (RI a i) x@RI{} = RI a (STJ i x)
unify (RI a i) x@RP{} = RI a (STJ i x)
unify (RI a i) x@RS{} = RI a (STJ i x)
unify x@RP{} (RI a i) = RI a (STJ i x)
unify x@RS{} (RI a i) = RI a (STJ i x)
unify (RP l1 r1) (RP l2 r2) = RP (unify l1 l2) (unify r1 r2)
unify (RS l1 r1) (RS l2 r2) = RS (unify l1 l2) (unify r1 r2)

instance Polynomial TRole where
  type (:*:) a b = 'RProd a b
  type (:+:) a b = 'RSum a b

-- fstI :: (Typeable a, Typeable b) => STId (a,b) n -> STId a (FstI n)
-- fstI (STI n) = STI n
-- fstI (STJ n r) = STJ (fstI n) (fstR r)

fstR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> FstR r1 ::: a
fstR (RI _ n) = RI PType n
fstR (RP a _) = a
fstR RA = RA

-- sndI :: (Typeable a, Typeable b) => STId (a,b) n -> STId a (FstI n)
-- sndI (STI n) = STI n
-- sndI (STJ n r) = STJ (fstI n) (fstR r)

sndR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> SndR r1 ::: b
sndR (RI _ n) = RI PType n
sndR (RP _ b) = b
sndR RA = RA

infix 9 :<:

-- Less-than role relation. A value of this type is a "path" to r1 from r2, if
-- r1 :<: r2

data (:<:) :: TRole -> TRole -> Type where
  LR :: r :<: r
  LTrans :: r1 :<: r2 -> r2 :<: r3 -> r1 :<: r3
  P1 :: r1 :<: 'RProd r1 r2
  P2 :: r2 :<: 'RProd r1 r2
  S1 :: 'RSum r1 r0 :<: r0
  S2 :: 'RSum r0 r1 :<: r0

  -- Congruence
  PC :: r1 :<: r3 -> r2 :<: r4 -> 'RProd r1 r2 :<: 'RProd r3 r4
  SC :: r1 :<: r3 -> r2 :<: r4 -> 'RSum r1 r2 :<: 'RSum r3 r4

ltFstR :: r1 ::: (a, b) -> FstR r1 :<: r1
ltFstR RI{} = LR
ltFstR RP{} = P1
ltFstR RA = LR

ltSndR :: r1 ::: (a, b) -> SndR r1 :<: r1
ltSndR RI{} = LR
ltSndR RP{} = P2
ltSndR RA = LR

infixr 1 :==>

data (:==>) :: TRole -> TRole -> Type where
  TComm  :: (Typeable a, Typeable b)
         => ri ::: a
         -> ro ::: b
         -> a :-> b
         -> ri :==> ro

  TDistr :: (Typeable a, Typeable b)
         => 'RId ri ::: a
         -> ro ::: b
         -> a :-> b
         -> 'RId ri :==> ro

  TSkip   :: (Typeable a, Typeable b)
          => ri ::: a
          -> ro ::: b
          -> ro :<: ri
          -> a :-> b
          -> ri :==> ro

  TSplit  :: ri :==> ro1
          -> ri :==> ro2
          -> ri :==> ro1 :*: ro2

  TSeq    :: Typeable a
          => r ::: a
          -> ri :==> r
          -> r  :==> ro
          -> ri :==> ro

  TBranch :: ri1 :==> ro1
          -> ri2 :==> ro2
          -> ri1 :+: ri2 :==> Unify ro1 ro2

{-
injRI :: 'RId n :~: 'RId m -> n :~: m
injRI Refl = Refl

injRP :: 'RProd a b :~: 'RProd c d -> (a :~: c, b :~: d)
injRP Refl = (Refl, Refl)

injRS :: 'RSum a b :~: 'RSum c d -> (a :~: c, b :~: d)
injRS Refl = (Refl, Refl)

injRL :: 'RSumL a :~: 'RSumL b -> a :~: b
injRL Refl = Refl

injRR :: 'RSumR a :~: 'RSumR b -> a :~: b
injRR Refl = Refl

eqR :: t1 ::: a -> t2 ::: b -> Decision (t1 :~: t2)
eqR (RI _ n) (RI _ m) =
  case n %~ m of
    Proved Refl -> Proved Refl
    Disproved f -> Disproved $ \x -> f (injRI x)
eqR (RP a b) (RP c d) =
  case (eqR a c, eqR b d) of
    (Proved Refl, Proved Refl) -> Proved Refl
    (Disproved f, _          ) -> Disproved $ \x -> f $ fst $ injRP x
    (_          , Disproved f) -> Disproved $ \x -> f $ snd $ injRP x
eqR (RS a b) (RS c d) =
  case (eqR a c, eqR b d) of
    (Proved Refl, Proved Refl) -> Proved Refl
    (Disproved f, _          ) -> Disproved $ \x -> f $ fst $ injRS x
    (_          , Disproved f) -> Disproved $ \x -> f $ snd $ injRS x
eqR (TL _ a) (TL _ b) =
  case eqR a b of
    Proved Refl -> Proved Refl
    Disproved f -> Disproved $ \x -> f $ injRL x
eqR (TR _ a) (TR _ b) =
  case eqR a b of
    Proved Refl -> Proved Refl
    Disproved f -> Disproved $ \x -> f $ injRR x
eqR _ _ = Disproved $ \x -> case x of {} -- XXX: Hack

toSRole :: t ::: a -> TRole
toSRole (RI _ i) = RId $ fromSing i
toSRole (RP a b) = RProd (toSRole a) (toSRole b)
toSRole (RS a b) = RSum  (toSRole a) (toSRole b)
toSRole (TL _ b) = RSumL (toSRole b)
toSRole (TR _ b) = RSumR (toSRole b)

data SomeRole t1 t2 a = forall t. Join (t ::: a, t1 :+: t2 :==> t)

-- rjoin :: (RoleGen m, Typeable a) => r1 ::: a -> r2 ::: a -> m (SomeRole r1 r2 a)
-- rjoin t1 t2 = case eqR t1 t2 of
--                 Proved Refl ->
--                   return $ Join (t1, TSkip (RS t1 t1) t1 (S3 LR) (id ||| id))
--                 Disproved _ -> withFreshId $ \i -> do
--                   let r = RI PType i
--                   return $ Join (r, TComm (RS t1 t2) r (id ||| id))

-}

class Monad m => RoleGen m where
  fresh :: m Nat
  keep  :: m a -> m a

-- joinR :: TRole -> TRole -> m Role

type STR = (Nat, Map TRole Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (S r, m) >> return r
  keep c = get >>= \(i, _) -> c >>= \a -> get >>= \(_, m) -> put (i, m) >> return a
--   joinR (RId n) (RId m)
--     | n == m = return $ Rol $ natToInt n
--   joinR a b = get >>= \(r, m) ->
--       let rol = Rol $ natToInt r
--           newm = Map.insert a rol $ Map.insert b rol m
--       in maybe (put (S r, newm) *> return rol) return (lookupR m)
--     where
--       lookupR m = maybe (maybe Nothing Just $ Map.lookup b m)
--                         Just
--                         (Map.lookup a m)

data ECore = forall a b. ECore (a :-> b)

instance Pretty ECore where
  pretty (ECore f) = pretty f

newtype Ty = Ty TypeRep

instance Pretty Ty where
  pretty (Ty t) = pretty $ show t

type Proto = GT Ty ECore

data DPair b t1 where
  DPair :: forall b t1 t2. t2 ::: b -> t1 :==> t2 -> DPair b t1

data (:=>) a b = Gen {
  getGen :: forall t1 m. (Typeable a, Typeable b, RoleGen m)
         =>  t1 ::: a -> m (DPair b t1)
  }

withFreshId :: RoleGen m => (forall i. SNat i -> m b) -> m b
withFreshId f = fresh >>= \i -> withSomeSing i f

withNewRole :: RoleGen m => PType a -> (forall r. 'RId r ::: a -> m b) -> m b
withNewRole a f = withFreshId $ \i -> f (RI a (STI i))

gId :: forall a. Typeable a => a :=> a
gId = Gen $ \r1 -> return $ DPair r1 $ TSkip r1 r1 LR id

gComp :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => b :=> c -> a :=> b -> a :=> c
gComp f g
  = Gen $ \r1 -> do
      DPair rt p1 <- getGen g r1
      DPair ro p2 <- getGen f rt
      return $ DPair ro $ TSeq rt p1 p2

instance Category (:=>) where
  type C (:=>) a = Typeable a
  id = gId
  (.) = gComp

wrap :: forall a b. (Typeable a, Typeable b) => a :-> b -> a :=> b
wrap f = Gen $ \ri -> withNewRole PType $ \ro -> return $ DPair ro $ TComm ri ro f

gFst :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> a
gFst = Gen $ \r1 -> do
  let r2 = fstR r1
  return $ DPair r2 $ TSkip r1 r2 (ltFstR r1) fst

gSnd :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> b
gSnd = Gen $ \r1 -> do
  let r2 = sndR r1
  return $ DPair r2 $ TSkip r1 r2 (ltSndR r1) snd

gSplit :: forall a b c. (Typeable a, Typeable b, Typeable c)
       => a :=> b -> a :=> c -> a :=> (b, c)
gSplit f g
  = Gen $ \r1 -> do
      DPair o1 p1 <- getGen f r1
      DPair o2 p2 <- getGen g r1
      return $ DPair (RP o1 o2) (TSplit p1 p2)

gProd :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d)
      => a :=> b -> c :=> d -> (a, c) :=> (b, d)
gProd f g = gSplit (f . gFst) (g . gSnd)

instance Show a => Const a (:=>) where
  const x = wrap (const x)

instance Arrow (:=>) where
  arr s f = wrap (arr s f)
  fst = gFst
  snd = gSnd
  (***) = gProd
  (&&&) = gSplit


gInl :: forall a b. (Typeable a, Typeable b)
     => a :=> Either a b
gInl = Gen $ \r1 -> do
         let o = RS r1 RA
         return $ DPair o (TSkip r1 o S2 inl)

gInr :: forall a b. (Typeable a, Typeable b)
     => b :=> Either a b
gInr = Gen $ \r1 -> do
         let o = RS RA r1
         return $ DPair o (TSkip r1 o S1 inr)

data APrefix r a b where
  APrefix :: forall a b r t1 t2. t1 ::: a -> t2 ::: b -> r :==> t1 :+: t2 -> APrefix r a b

ltSum :: n ::: a -> 'RSum n n :<: n
ltSum _ = S1

splitR :: (Typeable a, Typeable b)
       => r ::: Either a b -> APrefix r a b
splitR ri@RA = APrefix RA RA $ TSkip ri (RS RA RA) S1 id
splitR ri@(RI _ n) =
  let rl = RI PType n
      rr = RI PType n
  in APrefix rl rr $ TSkip ri (RS rl rr) S1 id
splitR ri@(RS a b) = APrefix a b $ TSkip ri ri LR id

gCase :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => a :=> c -> b :=> c -> Either a b :=> c
gCase f g = Gen $ \ri ->
  case splitR ri of
    APrefix l r c -> do
      DPair o1 p1 <- getGen f l
      DPair o2 p2 <- getGen g r
      return $ DPair (unify o1 o2) $
        TSeq (RS l r) c (TBranch p1 p2)

gSum :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d)
     => a :=> c -> b :=> d -> Either a b :=> Either c d
gSum f g = gCase (gInl . f) (gInr . g)

instance ArrowChoice (:=>) where
  inl = gInl
  inr = gInr
  (+++) = gSum
  (|||) = gCase

gfmap :: forall a b f. (IsC Typeable f a, IsC Typeable f b)
      => SPoly f
      -> (:=>) a b
      -> (:=>) (f :@: a) (f :@: b)
gfmap (FK _) _ = id
gfmap FId g = g
gfmap (FProd p1 p2) f = gfmap p1 f *** gfmap p2 f
gfmap (FSum p1 p2) f  = gfmap p1 f +++ gfmap p2 f

generate :: forall a b. (Typeable a, Typeable b) => a :=> b -> Proto
generate g = evalState pgen ((S Z, Map.empty)::STR)
  where
    pgen    = do
      DPair _ p <- getGen g ri
      gen p
    ri = RI PType (STI (sing :: SNat 'Z))

toId :: STId a -> TId
toId (STI n) = TI $ fromSing n
toId (STJ n r) = TJ (toId n) (toSRole r)

toSRole :: r ::: a -> TRole
toSRole (RI _ a) = RId $ toId a
toSRole (RS a b) = RSum (toSRole a) (toSRole b)
toSRole (RP a b) = RProd (toSRole a) (toSRole b)
toSRole  RA      = RAny

flatten :: RoleGen m => TRole -> m [Role]
flatten = undefined
-- flatten (RId   i) = return [Rol $ natToInt i]
-- flatten (RProd a b) = (++) <$> flatten a <*> flatten b
-- flatten (RSum r1 r2) = (:[]) <$> joinR r1 r2
-- flatten _ = error "Panic! Ill-formed protocol: Any can only occur \
--                   \ as part of RSum"

getTypeOf :: forall t1 a. Typeable a => t1 ::: a -> TypeRep
getTypeOf _ = typeRep (Proxy :: Proxy a)

gen :: RoleGen m => r1 :==> r2 -> m Proto
gen (TComm ri ro f)
  = fmap Comm $
    Msg <$> flatten (toSRole ri)
        <*> flatten (toSRole ro)
        <*> pure (Ty $ getTypeOf ri)
        <*> pure (ECore f)
gen (TDistr ri ro f)
  = fmap Comm $
    Msg <$> flatten (toSRole ri)
        <*> flatten (toSRole ro)
        <*> pure (Ty $ getTypeOf ri)
        <*> pure (ECore f)
gen (TSplit x1 x2)
  = go <$> gen x1 <*> gen x2
  where
    go GSkip g = g
    go g GSkip = g
    go g1 g2   = GComp Par g1 g2
gen (TSeq _ x2 x3) = go <$> gen x2 <*> gen x3
  where
    go GSkip g = g
    go g GSkip = g
    go g1 g2   = GComp Seq g1 g2
gen (TBranch x1 x2) = genBranch x1 x2
gen (TSkip _ _ _ _) = pure GSkip

genBranch :: RoleGen m => r1 :==> r2 -> r3 :==> r4 -> m Proto
genBranch = undefined

{-

data AnyRole t = forall a. Typeable a => AnyRole (t ::: a)

inR :: r1 :==> r2 -> AnyRole r1
inR (TComm r1 _ _) = AnyRole r1
inR (TDistr r1 _ _) = AnyRole r1
inR (TSplit r1 _) = inR r1
inR (TSeq _ r1 _) = inR r1
inR (TBranch r1 r2)
  = case (inR r1, inR r2) of
      (AnyRole a, AnyRole b) -> AnyRole (RS (TL PType a) (TR PType b))
inR (TSkip r _ _ _) = AnyRole r

sumt :: PType a -> PType b -> PType (Either a b)
sumt PType PType = PType

-- test = TSeq (RS (RI a r) (RI b s))
--             (TComm (RI a t) (TL (RI a r)) Inl)
--             (TBranch (TComm (RI a r) (RI a t) Id)
--                      (TComm (RI b s) (RI a t) (Const Unit)))
--   where
--     a = STUnit
--     b = STPrim SInt32
--     r = sing :: SNat 0
--     s = sing :: SNat 1
--     t = sing :: SNat 2


-- -- Sums:




genBranch x1 x2
  = case (inR x1, inR x2) of
      (AnyRole r1, AnyRole r2) ->
        let t1 = toSRole r1
            t2 = toSRole r2
        in br r1 r2
              <$> joinR t1 t2
              <*> flatten t1 <*> flatten t2
              <*> gen x1 <*> gen x2
  where
    br _ _ _ _ _ GSkip GSkip
      = GSkip
    br r1 r2 i i1 i2 a b
      = Choice i $ addAlt 0 (seqm (msg i i1 r1) a)
                 $ addAlt 1 (seqm (msg i i2 r2) b)
                 $ emptyAlt
    seqm GSkip = id
    seqm a     = GComp Seq a
    msg :: forall t a. Typeable a => Role -> [Role] -> t ::: a -> Proto
    msg f t pt
      | [f] == t = GSkip
      | otherwise = Comm $ Msg [f] t (Ty $ getTypeOf pt) (ECore (id :: a :-> a))
-}

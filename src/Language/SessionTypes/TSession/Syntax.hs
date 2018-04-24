{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
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
module Language.SessionTypes.TSession.Syntax
where

import Prelude hiding ( (.), id )

import Data.Kind hiding ( Type )

import Data.Singletons
import Data.Singletons.Decide
import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Category
import Control.Monad.State.Strict hiding ( lift )

import Language.Poly.C
import Language.Poly.Core hiding ( Nat, getType )
import Language.Poly.Type
import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt )
import Language.SessionTypes.Prefix.Global

data Idx = Z | S Idx
  deriving (Eq, Ord)

instance Show Idx where
  show = show . idxToInt

idxToInt :: Idx -> Int
idxToInt = go 0
  where
    go m Z = m
    go m (S n) = go (1+m) n

data instance Sing (t :: Idx) where
  SZ :: Sing 'Z
  SS :: Sing  n -> Sing ('S n)

ssInj :: 'S i :~: 'S j -> i :~: j
ssInj Refl = Refl

instance SDecide Idx where
  SZ %~ SZ = Proved Refl
  SZ %~ SS _ = Disproved (\x -> case x of {} )
  SS _ %~ SZ = Disproved (\x -> case x of {} )
  SS i %~ SS j = case i %~ j of
                   Proved Refl -> Proved Refl
                   Disproved f -> Disproved (\x -> f (ssInj x))

type SIdx (t :: Idx) = Sing t

type SomeIdx = SomeSing Idx

instance SingI 'Z where
  sing = SZ
instance SingI n => SingI ('S n) where
  sing = SS sing

instance SingKind Idx where
  type DemoteRep Idx = Idx

  fromSing SZ = Z
  fromSing (SS n) = S (fromSing n)

  toSing Z = SomeSing SZ
  toSing (S n) = withSomeSing n (SomeSing . SS)

data SRole
  = SId (Type TyPrim) Idx
  | SProd SRole SRole
  | SSum SRole SRole
  | SAny

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.
data TRole
  = RId   Idx
  | RProd TRole TRole
  | RSum  TRole TRole
  | RSumL TRole
  | RSumR TRole
  deriving (Eq, Ord, Show)

type family Unify (t1 :: TRole) (t2 :: TRole) :: TRole where
  Unify ('RId i) ('RId i)             = 'RId i
  Unify ('RProd r1 r2) ('RProd r3 r4) = 'RProd (Unify r1 r3) (Unify r2 r4)
  Unify ('RSum  r1 r2) ('RSum  r3 r4) = 'RSum (Unify r1 r3) (Unify r2 r4)
  Unify ('RSumL r1)  ('RSumR r2)      = 'RSum r1 r2
  Unify ('RSumL r1)  ('RSumL r2)      = 'RSumL (Unify r1 r2)
  Unify ('RSumL r1)  ('RSum r r2)     = 'RSum (Unify r1 r) r2
  Unify ('RSum r r2) ('RSumL r1)      = 'RSum (Unify r r1) r2
  Unify ('RSum r1 r) ('RSumR r2)      = 'RSum r1 (Unify r r2)
  Unify ('RSumR r2)  ('RSumL r1)      = 'RSum r1 r2
  Unify ('RSumR r1)  ('RSumR r2)      = 'RSumR (Unify r1 r2)
  Unify ('RSumR r2)  ('RSum r1 r)     = 'RSum r1 (Unify r2 r)

infixl 6 :+:
infixl 7 :*:
infix 5 :::

type (:*:) = 'RProd
type (:+:) = 'RSum

data (:::) (t :: TRole) (a :: Type TyPrim)  where
  RI :: SType t -> SIdx n    -> 'RId n       ::: t
  RP :: r1 ::: a -> r2 ::: b -> 'RProd r1 r2 ::: 'TProd a b
  RS :: r1 ::: a -> r2 ::: b -> 'RSum r1 r2  ::: 'TSum a b
  TL :: SType b  -> r1 ::: a -> 'RSumL r1    ::: 'TSum a b
  TR :: SType a  -> r2 ::: b -> 'RSumR r2    ::: 'TSum a b

getType :: t ::: a -> SType a
getType (RI t _) = t
getType (TL t r) = STSum (getType r) t
getType (TR t r) = STSum t (getType r)
getType (RS l r) = STSum (getType l) (getType r)
getType (RP l r) = STProd (getType l) (getType r)

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

eqR :: t1 ::: a -> t2 ::: a -> Decision (t1 :~: t2)
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

data SomeRole t1 t2 a = forall t. Join (t ::: a, t1 :==> t, t2 :==> t)


rjoin :: RoleGen m => t1 ::: a -> t2 ::: a -> m (SomeRole t1 t2 a)
rjoin i1@(TL _ a) i2@(TR _ b)
  = return $ Join (RS a b, TSkip i1 (S3 LR), TSkip i2 (S4 LR))
rjoin i2@(TR _ a) i1@(TL _ b)
  = return $ Join (RS b a, TSkip i2 (S4 LR), TSkip i1 (S3 LR))
rjoin a b
   | Proved Refl <- eqR a b = return $ Join (a, TSkip a LR, TSkip a LR)
   | otherwise             = withFreshId $ \i -> do
        let o = RI (getType a) i
        return $ Join (o, TComm a o Id, TComm b o Id)

unify :: t1 ::: a -> t2 ::: a -> Maybe (Unify t1 t2 ::: a)
unify (RI t1 n1) (RI t2 n2) =
    case (t1 %~ t2, n1 %~ n2) of
      (Proved Refl, Proved Refl) -> Just (RI t1 n1)
      _                          -> Nothing
unify (RP p1 p2) (RP p3 p4) =
    case (unify p1 p3, unify p2 p4) of
      (Just p13, Just p24) -> Just (RP p13 p24)
      _                    -> Nothing
unify (RS p1 p2) (RS p3 p4) =
    case (unify p1 p3, unify p2 p4) of
      (Just p13, Just p24) -> Just (RS p13 p24)
      _                    -> Nothing
unify (RS p1 p2) (TL _ p3) =
    case (unify p1 p3) of
      Just p13 -> Just (RS p13 p2)
      _        -> Nothing
unify (RS p1 p2) (TR _ p4) =
    case (unify p2 p4) of
      Just p24 -> Just (RS p1 p24)
      _        -> Nothing
unify (TL _ p3) (RS p1 p2) =
    case (unify p3 p1) of
      Just p13 -> Just (RS p13 p2)
      _        -> Nothing
unify (TR _ p4) (RS p1 p2) =
    case (unify p4 p2) of
      Just p24 -> Just (RS p1 p24)
      _        -> Nothing
unify (TL a p1) (TL _ p2) =
    case (unify p1 p2) of
      Just p3 -> Just (TL a p3)
      _        -> Nothing
unify (TR a p1) (TR _ p2) =
    case (unify p1 p2) of
      Just p3 -> Just (TR a p3)
      _        -> Nothing
unify (TL _ p1) (TR _ p2) = Just (RS p1 p2)
unify (TR _ p1) (TL _ p2) = Just (RS p2 p1)
unify (RI _ _) _ = Nothing
unify _ (RI _ _) = Nothing

class Monad m => RoleGen m where
   fresh :: m Idx
   joinR :: TRole -> TRole -> m Role

type STR = (Idx, Map TRole Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (S r, m) >> return r
  joinR (RId n) (RId m)
    | n == m = return $ Rol $ idxToInt n
  joinR a b = get >>= \(r, m) ->
      let rol = Rol $ idxToInt r
          newm = Map.insert a rol $ Map.insert b rol m
      in maybe (put (S r, newm) *> return rol) return (lookupR m)
    where
      lookupR m = maybe (maybe Nothing Just $ Map.lookup b m)
                        Just
                        (Map.lookup a m)

infix 9 :<:

data (:<:) :: TRole -> TRole -> * where
  LR :: r :<: r
  P1 :: r1 :<: r2 -> r1 :<: 'RProd r2 r3
  P2 :: r1 :<: r3 -> r1 :<: 'RProd r2 r3
  S1 :: r1 :<: r2 -> 'RSumL r1 :<: r2
  S2 :: r1 :<: r2 -> 'RSumR r1 :<: r2
  S3 :: r1 :<: r2 -> 'RSum r1 r3 :<: 'RSumL r2
  S4 :: r1 :<: r2 ->'RSum r3 r1 :<: 'RSumR r2

infixr 1 :==>

data (:==>) :: TRole -> TRole -> * where
  TComm  :: ri ::: a
         -> ro ::: b
         -> CCore (a :-> b)
         -> ri :==> ro

  TSplit  :: ri :==> ro1
          -> ri :==> ro2
          -> ri :==> ro1 :*: ro2

  TSeq    :: r ::: a
          -> ri :==> r
          -> r  :==> ro
          -> ri :==> ro

  TBranchI :: ri :==> ro
           -> ri :==> ro
           -> ri :==> ro

  TBranchJ :: ri1 :==> ro
           -> ri2 :==> ro
           -> ri1 :+: ri2 :==> ro

  TBranchL :: ri1 :==> ro
           -> 'RSumL ri1 :==> ro

  TBranchR :: ri2 :==> ro
           -> 'RSumR ri2 :==> ro

  TSkip   :: ri ::: a
          -> ro :<: ri
          -> ri :==> ro

inR :: r1 :==> r2 -> TRole
inR (TComm r1 _ _) = toSRole r1
inR (TSplit r1 _) = inR r1
inR (TSeq _ r1 _) = inR r1
inR (TBranchI r1 _) = inR r1
inR (TBranchJ r1 r2) = RSum (inR r1) (inR r2)
inR (TBranchL r1) = RSumL (inR r1)
inR (TBranchR r1) = RSumR (inR r1)
inR (TSkip r _) = toSRole r

inTy :: r1 :==> r2 -> SomeSing (Type TyPrim)
inTy (TComm r1 _ _) = SomeSing $ getType r1
inTy (TSkip r _) = SomeSing $ getType r
inTy (TSplit r1 _) = inTy r1
inTy (TSeq _ r1 _) = inTy r1
inTy (TBranchI r1 r2)
  = case (inTy r1, inTy r2) of
      (SomeSing tr1, SomeSing tr2) -> SomeSing $ STSum tr1 tr2
inTy (TBranchJ r1 r2)
  = case (inTy r1, inTy r2) of
      (SomeSing tr1, SomeSing tr2) -> SomeSing $ STSum tr1 tr2
inTy (TBranchL r1) = inTy r1
inTy (TBranchR r1) = inTy r1

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

type Proto = GT CType ECore

data DPair b t1 = forall t2. DPair (t2 ::: b) (t1 :==> t2)

data (:=>) a b
  = Gen { getGen2 :: forall t1 t2 m. RoleGen m
                  => t1 ::: a -> t2 ::: b -> m (t1 :==> t2)
        , getGen1 :: forall t1 m. RoleGen m =>  t1 ::: a -> m (DPair b t1) }

idxOf :: r1 ::: a -> [Idx]
idxOf (RI _ i) = [fromSing i]
idxOf (RP a b) = idxOf a ++ idxOf b
idxOf (RS _ _) = []
idxOf (TL _ _) = []
idxOf (TR _ _) = []

disjoint :: r1 ::: a -> r2 ::: b -> Bool
disjoint r1 r2 = all (`notElem` r2l) $ idxOf r1
  where
   r2l = idxOf r2

comm :: RoleGen m => r1 ::: a -> r2 ::: b -> CCore (a :-> b) -> m (r1 :==> r2)
comm r1 r2 f
  | disjoint r1 r2 = return $ TComm r1 r2 f
  | otherwise = withFreshId $ \i -> do
      let r = RI (getType r2) i
      TSeq r <$> comm r1 r f <*> comm r r2 Id

gId :: forall a. a :=> a
gId
  = Gen
  { getGen1 = \r1 -> return $ DPair r1 $ TSkip r1 LR
  , getGen2 = \r1 r2 ->
                case eqR r1 r2 of
                  Proved Refl -> return $ TSkip r1 LR
                  Disproved _ -> comm r1 r2 Id
  }

gComp :: forall a b c. b :=> c -> a :=> b -> a :=> c
gComp f g
  = Gen
  { getGen1 = \r1 -> do
      DPair r2 p1 <- getGen1 g r1
      DPair r3 p2 <- getGen1 f r2
      return $ DPair r3 (TSeq r2 p1 p2)
  , getGen2 = \r1 r2 -> do
      DPair rt p1 <- getGen1 g r1
      p2 <- getGen2 f rt r2
      return $ TSeq rt p1 p2
  }

instance Category (:=>) where
  id = gId
  (.) = gComp

-- Instance Arrow fails because (:=>) has to have type (a -> b). FIXME:
-- generalise arrows, or move my Language.Poly.C to Haskell types?

withFreshId :: RoleGen m => (forall i. SIdx i -> m b) -> m b
withFreshId f = fresh >>= \i -> withSomeSing i f

embed :: forall a b t1 m. (SingI (a :-> b), RoleGen m)
      => t1 ::: a -> CCore (a :-> b) -> m (DPair b t1)
embed ri f = withFreshId $ \i -> do
    let r = RI sb i
    DPair r <$> comm ri r f
  where
    sb = case sing :: SType (a :-> b) of
           STArr _ b -> b

embedS :: forall a b t1 m. RoleGen m
      => Sing (a :-> b) -> t1 ::: a -> CCore (a :-> b) -> m (DPair b t1)
embedS (singInstance -> SingInstance) ri f = embed ri f

lift :: forall a b. SingI (a :-> b) => CCore (a :-> b) -> a :=> b
lift Id = gId
lift Fst = gFst
lift Snd = gSnd
lift Inl = case sing :: SType (a :-> b) of
             STArr _ (STSum _ b) -> case singInstance b of
                                     SingInstance -> gInl
             _ -> error "Panic! Impossible case: ill-typed GADT"
lift Inr = case sing :: SType (a :-> b) of
             STArr _ (STSum a _) -> case singInstance a of
                                     SingInstance -> gInr
             _ -> error "Panic! Impossible case: ill-typed GADT"
lift (Split f g) = gSplit (lift f) (lift g)
lift f
  = Gen
  { getGen1 = \ri -> embed ri f
  , getGen2 = \ri ro -> comm ri ro f
  }

liftS :: forall a b. Sing (a :-> b) -> CCore (a :-> b) -> a :=> b
liftS (singInstance -> SingInstance) f = lift f


gFst :: forall a b. 'TProd a b :=> a
gFst
  = Gen
  { getGen1 = \r1 ->
     case r1 of
       RP r11            _ -> return $ DPair r11 (TSkip r1 (P1 LR))
       (RI t@(STProd a _) _) -> embedS (STArr t a) r1 Fst
  , getGen2 = \r1 r2 ->
     case r1 of
       RP r11 _ -> TSeq r11 (TSkip r1 (P1 LR)) <$> getGen2 gId r11 r2
       _      -> comm r1 r2 Fst
  }

gSnd :: forall a b. 'TProd a b :=> b
gSnd
  = Gen
  { getGen1 = \r1 ->
     case r1 of
       RP _ r12            -> return $ DPair r12 (TSkip r1 (P2 LR))
       (RI t@(STProd _ b) _) -> embedS (STArr t b) r1 Snd
  , getGen2 = \r1 r2 ->
     case r1 of
       RP _ r12 -> TSeq r12 (TSkip r1 (P2 LR)) <$> getGen2 gId r12 r2
       _      -> comm r1 r2 Snd
  }

gSplit :: forall a b c. a :=> b -> a :=> c -> a :=> 'TProd b c
gSplit f g
  = Gen
  { getGen1 = \r1 -> do
      DPair o1 p1 <- getGen1 f r1
      DPair o2 p2 <- getGen1 g r1
      return $ DPair (RP o1 o2) (TSplit p1 p2)
  , getGen2 = \r1 r2 -> do
      DPair o1 p1 <- getGen1 f r1
      DPair o2 p2 <- getGen1 g r1
      p3 <- getGen2 id (RP o1 o2) r2
      return $ TSeq (RP o1 o2) (TSplit p1 p2) p3
  }


gProd :: forall a b c d. a :=> b -> c :=> d -> 'TProd a c :=> 'TProd b d
gProd f g = gSplit (f . gFst) (g . gSnd)

-- -- Sums:

gInl :: forall a b. SingI b => a :=> 'TSum a b
gInl
  = Gen
  { getGen1 = \r1 ->
      return $ DPair (TL (sing :: SType b) r1) (TSkip r1 (S1 LR))
  , getGen2 = \r1 r2 -> comm r1 r2 Inl
  }

gInr :: forall a b. SingI a => b :=> 'TSum a b
gInr
  = Gen
  { getGen1 = \r1 ->
      return $ DPair (TR (sing :: SType a) r1) (TSkip r1 (S2 LR))
  , getGen2 = \r1 r2 -> comm r1 r2 Inr
  }

gCase :: forall a b c. a :=> c -> b :=> c -> 'TSum a b :=> c
gCase f g
  = Gen
  { getGen1 = \r1 ->
      case r1 of
       RS l r -> do
           DPair o1 p1 <- getGen1 f l
           DPair o2 p2 <- getGen1 g r
           Join (o, g1, g2) <- rjoin o1 o2
           return $ DPair o $ TBranchJ (TSeq o1 p1 g1) (TSeq o2 p2 g2)
       TL _ l -> do
           DPair o1 p1 <- getGen1 f l
           return $ DPair o1 (TBranchL p1)

       TR _ l -> do
           DPair o1 p1 <- getGen1 g l
           return $ DPair o1 (TBranchR p1)

       RI (STSum a b) n -> do
           DPair o1 p1 <- getGen1 f (RI a n)
           DPair o2 p2 <- getGen1 g (RI b n)
           Join (o, g1, g2) <- rjoin o1 o2
           return $ DPair o $ TBranchI (TSeq o1 p1 g1) (TSeq o2 p2 g2)
  , getGen2 =  \r1 r2 ->
      case r1 of
       RS l r -> do
           p1 <- getGen2 f l r2
           p2 <- getGen2 g r r2
           return $ TBranchJ p1 p2
       TL _ l -> TBranchL <$> getGen2 f l r2

       TR _ l -> TBranchR <$> getGen2 g l r2

       RI (STSum a b) n -> do
           p1 <- getGen2 f (RI a n) r2
           p2 <- getGen2 g (RI b n) r2
           return $ TBranchI p1 p2
  }

gsum :: forall a b c d. (SingI c, SingI d)
     => a :=> c -> b :=> d -> 'TSum a b :=> 'TSum c d
gsum f g = gCase (gInl . f) (gInr . g)

gfmap :: forall r1 r2 f. (SingI r1, SingI r2)
      => Sing f
      -> (:=>) r1 r2
      -> (:=>) (f :@: r1) (f :@: r2)
gfmap (SPK _) _ = id
gfmap SPId g = g
gfmap (SPProd p1 p2) f = gProd (gfmap p1 f) (gfmap p2 f)
gfmap (SPSum p1 p2) f
  = case (appD p1 (sing :: Sing r2), appD p2 (sing :: Sing r2)) of
        (SingInstance, SingInstance) -> gsum (gfmap p1 f) (gfmap p2 f)

generate :: forall a b. (SingI a, SingI b) => a :=> b -> Proto
generate g = evalState (pgen >>= gen) ((S Z, Map.empty)::STR)
  where
    pgen    = getGen2 g (RI (sing :: Sing a) (sing :: Sing 'Z))
                        (RI (sing :: Sing b) (sing :: Sing 'Z))

flatten :: RoleGen m => TRole -> m [Role]
flatten (RId   i) = return [Rol $ idxToInt i]
flatten (RProd a b) = (++) <$> flatten a <*> flatten b
flatten (RSum r1 r2) = (:[]) <$> joinR r1 r2
flatten _ = error "Panic! Ill-formed protocol: Any can only occur \
                  \ as part of RSum"

gen :: RoleGen m => r1 :==> r2 -> m Proto
gen (TComm ri ro f) = fmap Comm $
  Msg <$> flatten (toSRole ri)
      <*> flatten (toSRole ro)
      <*> pure (fromSing t1)
      <*> pure (eraseTy (STArr t1 t2) f)
  where
    t1 = getType ri
    t2 = getType ro
gen (TSplit x1 x2) = GComp Par <$> gen x1 <*> gen x2
gen (TSeq _ x2 x3) = GComp Seq <$> gen x2 <*> gen x3
gen (TBranchI x1 x2) = genBranch x1 x2
gen (TBranchJ x1 x2) = genBranch x1 x2
gen (TBranchL x1) = gen x1
gen (TBranchR x1) = gen x1
gen (TSkip _ _) = pure GSkip


genBranch :: RoleGen m => r1 :==> r2 -> r3 :==> r4 -> m Proto
genBranch x1 x2
  = br <$> joinR r1 r2 <*> flatten r1 <*> flatten r2 <*> gen x1 <*> gen x2
  where
    br i i1 i2 a b
      = case (t1, t2) of
          (SomeSing rt1, SomeSing rt2) ->
            Choice i $ addAlt 0 (GComp Seq (msg i i1 rt1) a)
                     $ addAlt 1 (GComp Seq (msg i i2 rt2) b)
                     $ emptyAlt
    msg f t pt
      | [f] == t = GSkip
      | otherwise = Comm $ Msg [f] t (fromSing pt) (eraseTy (STArr pt pt) Id)
    r1 = inR x1
    r2 = inR x2
    t1 = inTy x1
    t2 = inTy x2

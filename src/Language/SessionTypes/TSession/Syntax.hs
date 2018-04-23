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
import Data.List
  ( foldl'
  , nub )
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
  | RAny
  deriving (Eq, Ord)

type family Unify (t1 :: TRole) (t2 :: TRole) :: TRole where
  Unify 'RAny r = r
  Unify r 'RAny = r
  Unify ('RId i) ('RId i) = 'RId i
  Unify ('RProd r1 r2) ('RProd r3 r4) = 'RProd (Unify r1 r3) (Unify r2 r4)
  Unify ('RSum  r1 r2) ('RSum  r3 r4) = 'RSum (Unify r1 r3) (Unify r2 r4)

infixl 6 :+:
infixl 7 :*:

type (:*:) = 'RProd
type (:+:) = 'RSum

data STRole (a :: Type TyPrim) (t :: TRole) where
  RI :: SType t -> SIdx n          -> STRole t            ('RId n)
  RP :: STRole a r1 -> STRole b r2 -> STRole ('TProd a b) ('RProd r1 r2)
  RS :: STRole a r1 -> STRole b r2 -> STRole ('TSum a b)  ('RSum r1 r2)
  TL :: SType b -> STRole a r1     -> STRole ('TSum a b)  ('RSum r1 'RAny)
  TR :: SType a -> STRole b r2     -> STRole ('TSum a b)  ('RSum 'RAny r2)

toSRole :: STRole a t -> TRole
toSRole (RI _ i) = RId $ fromSing i
toSRole (RP a b) = RProd (toSRole a) (toSRole b)
toSRole (RS a b) = RSum  (toSRole a) (toSRole b)
toSRole (TL _ b) = RSum  (toSRole b) RAny
toSRole (TR _ b) = RSum  RAny (toSRole b)

unify :: STRole a t1 -> STRole a t2 -> Maybe (STRole a (Unify t1 t2))
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

type STR = (Idx, Map (TRole, TRole) Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (S r, m) >> return r
  joinR a b = get >>= \(r, m) ->
      let rol = Rol $ idxToInt r
          newm = foldl' (\nm s -> Map.insert s rol nm) m $ combinations a b
      in maybe (put (S r, newm) *> return rol) return (Map.lookup (a,b) m)
    where
      combinations r1 r2
        = nub $ filter (/= (RAny,RAny)) [(r1,r2), (r1,RAny), (RAny, r2)]

infix 9 :<:

data (:<:) :: TRole -> TRole -> * where
  LR :: r :<: r
  P1 :: r1 :<: r2 -> r1 :<: 'RProd r2 r3
  P2 :: r1 :<: r3 -> r1 :<: 'RProd r2 r3
  S1 :: r1 :<: r2 -> (r1 :+: r0) :<: r2
  S2 :: r1 :<: r2 -> (r0 :+: r1) :<: r2

infixr 1 :==>

data (:==>) :: TRole -> TRole -> * where
  TComm  :: STRole a ri
         -> STRole b ro
         -> CCore (a ':-> b)
         -> ri :==> ro

  TSplit  :: ri :==> ro1
          -> ri :==> ro2
          -> ri :==> ro1 :*: ro2

  TSeq    :: STRole a r
          -> ri :==> r
          -> r  :==> ro
          -> ri :==> ro

  TBranchI :: 'RId n :==> ro1
           -> 'RId n :==> ro2
           -> 'RId n :==> Unify ro1 ro2

  TBranchJ :: ri1 :==> ro1
           -> ri2 :==> ro2
           -> ri1 :+: ri2 :==> Unify ro1 ro2

  TBranchL :: ri1 :==> ro
           -> ri1 :+: ri2 :==> ro

  TBranchR :: ri2 :==> ro
           -> ri1 :+: ri2 :==> ro

  TSkip   :: STRole a ri
          -> ro :<: ri
          -> ri :==> ro

inR :: r1 :==> r2 -> TRole
inR (TComm r1 _ _) = toSRole r1
inR (TSplit r1 _) = inR r1
inR (TSeq _ r1 _) = inR r1
inR (TBranchI r1 _) = inR r1
inR (TBranchJ r1 r2) = RSum (inR r1) (inR r2)
inR (TBranchL r1) = RSum (inR r1) RAny
inR (TBranchR r1) = RSum RAny (inR r1)
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

data DPair b t1 = forall t2. DPair (STRole b t2) (t1 :==> t2)
newtype (:=>) a b
  = Gen { getGen :: forall t1 m. RoleGen m => STRole a t1 -> m (DPair b t1) }

gId :: forall a. a :=> a
gId = Gen $ \r1 -> pure $ DPair r1 (TSkip r1 LR)

gComp :: forall a b c. b :=> c -> a :=> b -> a :=> c
gComp f g = Gen $ \r1 -> do
    DPair r2 p1 <- getGen g r1
    DPair r3 p2 <- getGen f r2
    return $ DPair r3 (TSeq r2 p1 p2)

instance Category (:=>) where
  id = gId
  (.) = gComp

-- Instance Arrow fails because (:=>) has to have type (a -> b). FIXME:
-- generalise arrows, or move my Language.Poly.C to Haskell types?

-- If we get a pair of roles, we just skip, with the left or right role as
-- output role.
-- If we get a single role, we lift the "fst" function
gfst :: forall a b. 'TProd a b :=> a
gfst = Gen $ \r1 ->
    case r1 of
      RP r11            _ -> return $ DPair r11 (TSkip r1 (P1 LR))
      (RI (STProd a _) _) -> getGen (liftS a Fst) r1

gsnd :: forall a b. 'TProd a b :=> b
gsnd = Gen $ \r1 ->
    case r1 of
      RP _ r12            -> return $ DPair r12 (TSkip r1 (P2 LR))
      (RI (STProd _ b) _) -> getGen (liftS b Snd) r1

gsplit :: forall a b c. a :=> b -> a :=> c -> a :=> 'TProd b c
gsplit f g = Gen $ \r1 -> do
   DPair o1 p1 <- getGen f r1
   DPair o2 p2 <- getGen g r1
   return $ DPair (RP o1 o2) (TSplit p1 p2)

lift :: forall a b. SingI b => CCore (a ':-> b) -> a :=> b
lift f = Gen $ \ri -> do
      SomeSing i <- toSing <$> fresh
      let r = RI (sing :: Sing b) i
      return $ DPair r (TComm ri r f)

liftS :: forall a b. Sing b -> CCore (a ':-> b) -> a :=> b
liftS (singInstance -> SingInstance) f = lift f

gprod :: forall a b c d. a :=> b -> c :=> d -> 'TProd a c :=> 'TProd b d
gprod f g = gsplit (f . gfst) (g . gsnd)

-- Sums:

gInl :: forall a b. SingI b => a :=> 'TSum a b
gInl = Gen $ \r1 -> return $ DPair (TL (sing :: SType b) r1) (TSkip r1 (S1 LR))

gInr :: forall a b. SingI a => b :=> 'TSum a b
gInr = Gen $ \r1 -> return $ DPair (TR (sing :: SType a) r1) (TSkip r1 (S2 LR))

getType :: STRole a t -> SType a
getType (RI t _) = t
getType (TL t r) = STSum (getType r) t
getType (TR t r) = STSum t (getType r)
getType (RS l r) = STSum (getType l) (getType r)
getType (RP l r) = STProd (getType l) (getType r)

gCase :: forall a b c. a :=> c -> b :=> c -> 'TSum a b :=> c
gCase f g = Gen $ \r1 ->
    case r1 of
      RS l r -> do
          DPair o1 p1 <- getGen f l
          DPair o2 p2 <- getGen g r
          case unify o1 o2 of
            Just o -> return $ DPair o $ TBranchJ p1 p2
            Nothing -> do
              SomeSing i <- toSing <$> fresh
              let o = RI (getType o1) i
              return $ DPair o (TBranchJ (TSeq o1 p1 (TComm o1 o Id))
                                         (TSeq o2 p2 (TComm o2 o Id)))
      TL _ l -> do
          DPair o1 p1 <- getGen f l
          return $ DPair o1 (TBranchL p1)

      TR _ l -> do
          DPair o1 p1 <- getGen g l
          return $ DPair o1 (TBranchR p1)

      RI (STSum a b) n -> do
          DPair o1 p1 <- getGen f (RI a n)
          DPair o2 p2 <- getGen g (RI b n)
          case unify o1 o2 of
            Just o -> return $ DPair o $ TBranchI p1 p2
            Nothing -> do
              SomeSing i <- toSing <$> fresh
              let o = RI (getType o1) i
              return $ DPair o (TBranchI (TSeq o1 p1 (TComm o1 o Id))
                                         (TSeq o2 p2 (TComm o2 o Id)))

gsum :: forall a b c d. (SingI c, SingI d)
     => a :=> c -> b :=> d -> 'TSum a b :=> 'TSum c d
gsum f g = gCase (gInl . f) (gInr . g)

gfmap :: forall r1 r2 f. (SingI r1, SingI r2)
      => Sing f
      -> (:=>) r1 r2
      -> (:=>) (f :@: r1) (f :@: r2)
gfmap (SPK _) _ = id
gfmap SPId g = g
gfmap (SPProd p1 p2) f = gprod (gfmap p1 f) (gfmap p2 f)
gfmap (SPSum p1 p2) f
  = case (appD p1 (sing :: Sing r2), appD p2 (sing :: Sing r2)) of
        (SingInstance, SingInstance) -> gsum (gfmap p1 f) (gfmap p2 f)

generate :: forall a b. SingI a => a :=> b -> Proto
generate g = evalState (gen $ wrap op) ((S f, m)::STR)
  where
    (op, (f, m)) = runState pgen ((S Z, Map.empty)::STR)
    pgen    = getGen g (RI (sing :: Sing a) (sing :: Sing 'Z))

flatten :: RoleGen m => TRole -> m [Role]
flatten (RId   i) = return [Rol $ idxToInt i]
flatten (RProd a b) = (++) <$> flatten a <*> flatten b
flatten (RSum r1 r2) = (:[]) <$> joinR r1 r2
flatten _ = error "Panic! Ill-formed protocol: Any can only occur \
                  \ as part of RSum"

wrap :: DPair a ('RId 'Z) -> 'RId 'Z :==> 'RId 'Z
wrap (DPair (RI _ SZ) p) = p
wrap (DPair o p) = TSeq o p (TComm o (RI (getType o) SZ) Id)

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
    msg f t pt = Comm $ Msg [f] t (fromSing pt) (eraseTy (STArr pt pt) Id)
    r1 = inR x1
    r2 = inR x2
    t1 = inTy x1
    t2 = inTy x2

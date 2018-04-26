{-# LANGUAGE TupleSections #-}
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

data SRole
  = forall a. SId (Proxy a) Nat
  | SProd SRole SRole
  | SSum SRole SRole
  | SAny

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.
data TRole
  = RId   Nat
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

infix 5 :::

instance Polynomial TRole where
  type (:*:) a b = 'RProd a b
  type (:+:) a b = 'RSum a b

data (:::) (t :: TRole) (a :: Type)  where
  RI :: PType t -> SNat n    -> 'RId n      ::: t
  RP :: r1 ::: a -> r2 ::: b -> 'RProd r1 r2 ::: (a, b)
  RS :: r1 ::: a -> r2 ::: b -> 'RSum r1 r2  ::: Either a b
  TL :: PType b  -> r1 ::: a -> 'RSumL r1    ::: Either a b
  TR :: PType a  -> r2 ::: b -> 'RSumR r2    ::: Either a b

getType :: Typeable a => t ::: a -> PType a
getType _ = PType

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

data SomeRole t1 t2 a = forall t. Join (t ::: a, t1 :==> t, t2 :==> t)


rjoin :: (Typeable a, RoleGen m) => t1 ::: a -> t2 ::: a -> m (SomeRole t1 t2 a)
rjoin i1@(TL _ a) i2@(TR _ b)
  = return $ Join (o, TSkip i1 o (S3 LR) id, TSkip i2 o (S4 LR) id)
  where
    o = RS a b
rjoin i2@(TR _ b) i1@(TL _ a)
  = return $ Join (o, TSkip i2 o (S4 LR) id, TSkip i1 o (S3 LR) id)
  where
    o = RS a b
rjoin a b
   | Proved Refl <- eqR a b =
       return $ Join (a, TSkip a a LR id, TSkip a a LR id)
   | otherwise = withFreshId $ \i -> do
       let o = RI PType i
       fmap Join $ (o,,) <$>  comm a o id <*> comm b o id

unify :: t1 ::: a -> t2 ::: a -> Maybe (Unify t1 t2 ::: a)
unify o@(RI _ a) (RI _ b) =
    case (a %~ b) of
      (Proved Refl) -> Just o
      _             -> Nothing
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
   fresh :: m Nat
   joinR :: TRole -> TRole -> m Role

type STR = (Nat, Map TRole Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (S r, m) >> return r
  joinR (RId n) (RId m)
    | n == m = return $ Rol $ natToInt n
  joinR a b = get >>= \(r, m) ->
      let rol = Rol $ natToInt r
          newm = Map.insert a rol $ Map.insert b rol m
      in maybe (put (S r, newm) *> return rol) return (lookupR m)
    where
      lookupR m = maybe (maybe Nothing Just $ Map.lookup b m)
                        Just
                        (Map.lookup a m)

infix 9 :<:

data (:<:) :: TRole -> TRole -> Type where
  LR :: r :<: r
  P1 :: r1 :<: r2 -> r1 :<: 'RProd r2 r3
  P2 :: r1 :<: r3 -> r1 :<: 'RProd r2 r3
  S1 :: r1 :<: r2 -> 'RSumL r1 :<: r2
  S2 :: r1 :<: r2 -> 'RSumR r1 :<: r2
  S3 :: r1 :<: r2 -> 'RSum r1 r3 :<: 'RSumL r2
  S4 :: r1 :<: r2 ->'RSum r3 r1 :<: 'RSumR r2

infixr 1 :==>

data (:==>) :: TRole -> TRole -> Type where
  TComm  :: (Typeable a, Typeable b)
         => ri ::: a
         -> ro ::: b
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

  TBranchI :: ri :==> ro
           -> ri :==> ro
           -> ri :==> ro

  TBranchJ :: ri1 :==> ro
           -> ri2 :==> ro
           -> ri1 :+: ri2 :==> ro

  TBranchL :: Typeable a
           => 'RSumL ri1 ::: a
           -> ri1 :==> ro
           -> 'RSumL ri1 :==> ro

  TBranchR :: Typeable a
           => 'RSumR ri2 ::: a
           -> ri2 :==> ro
           -> 'RSumR ri2 :==> ro

  TSkip   :: (Typeable a, Typeable b)
          => ri ::: a
          -> ro ::: b
          -> ro :<: ri
          -> a :-> b
          -> ri :==> ro

data AnyRole t = forall a. Typeable a => AnyRole (t ::: a)

inR :: r1 :==> r2 -> AnyRole r1
inR (TComm r1 _ _) = AnyRole r1
inR (TSplit r1 _) = inR r1
inR (TSeq _ r1 _) = inR r1
inR (TBranchI r1 _) = inR r1
inR (TBranchJ r1 r2)
  = case (inR r1, inR r2) of
      (AnyRole a, AnyRole b) -> AnyRole (RS a b)
inR (TBranchL r _) = AnyRole r
inR (TBranchR r _) = AnyRole r
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

data ECore = forall a b. ECore (a :-> b)

instance Pretty ECore where
  pretty (ECore f) = pretty f

newtype Ty = Ty TypeRep

instance Pretty Ty where
  pretty (Ty t) = pretty $ show t

type Proto = GT Ty ECore

data DPair b t1 = forall t2. DPair (t2 ::: b) (t1 :==> t2)

data (:=>) a b
  = Gen { getGen2 :: forall t1 t2 m. (Typeable a, Typeable b, RoleGen m)
                  => t1 ::: a -> t2 ::: b -> m (t1 :==> t2)
        , getGen1 :: forall t1 m. (Typeable a, Typeable b, RoleGen m)
                  =>  t1 ::: a -> m (DPair b t1) }

idxOf :: r1 ::: a -> [Nat]
idxOf (RI _ i) = [fromSing i]
idxOf (RP a b) = idxOf a ++ idxOf b
idxOf (RS _ _) = []
idxOf (TL _ _) = []
idxOf (TR _ _) = []

disjoint :: r1 ::: a -> r2 ::: b -> Bool
disjoint r1 r2 = all (`notElem` r2l) $ idxOf r1
  where
   r2l = idxOf r2

comm :: (Typeable a, Typeable b, RoleGen m)
     => r1 ::: a -> r2 ::: b -> a :-> b -> m (r1 :==> r2)
comm r1 r2 f
  | disjoint r1 r2 = return $ TComm r1 r2 f
  | otherwise = withFreshId $ \i -> do
      let r = RI PType i
      TSeq r <$> comm r1 r f <*> comm r r2 id

gId :: forall a. Typeable a => a :=> a
gId
  = Gen
  { getGen1 = \r1 -> return $ DPair r1 $ TSkip r1 r1 LR id
  , getGen2 = \r1 r2 ->
                case eqR r1 r2 of
                  Proved Refl -> return $ TSkip r1 r1 LR id
                  Disproved _ -> comm r1 r2 id
  }

gComp :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => b :=> c -> a :=> b -> a :=> c
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
  type C (:=>) a = Typeable a
  id = gId
  (.) = gComp

-- Instance Arrow fails because (:=>) has to have type (a -> b). FIXME:
-- generalise arrows, or move my Language.Poly.C to Haskell types?

withFreshId :: RoleGen m => (forall i. SNat i -> m b) -> m b
withFreshId f = fresh >>= \i -> withSomeSing i f

embed :: forall a b t1 m. (Typeable a, Typeable b, RoleGen m)
      => t1 ::: a -> a :-> b -> m (DPair b t1)
embed ri f = withFreshId $ \i -> do
     let r = RI PType i
     DPair r <$> comm ri r f

lift :: forall a b. (Typeable a, Typeable b) => a :-> b -> a :=> b
lift IdF = gId
lift (FstF) = gFst
lift (SndF) = gSnd
lift (InlF) = gInl
lift (InrF) = gInr
-- -- lift (SplitF f g) = gSplit (lift f) (lift g)
lift f
  = Gen
  { getGen1 = \ri -> embed ri f
  , getGen2 = \ri ro -> comm ri ro f
  }

gFst :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> a
gFst
  = Gen
  { getGen1 = \r1 ->
     case r1 of
       RP r11 _ -> return $ DPair r11 (TSkip r1 r11 (P1 LR) fst)
       RI _ _ -> embed r1 fst
  , getGen2 = \r1 r2 ->
     case r1 of
       RP r11 _ -> TSeq r11 (TSkip r1 r11 (P1 LR) fst) <$> getGen2 gId r11 r2
       _      -> comm r1 r2 fst
  }

gSnd :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> b
gSnd
  = Gen
  { getGen1 = \r1 ->
     case r1 of
       RP _ r12 -> return $ DPair r12 (TSkip r1 r12 (P2 LR) snd)
       (RI _ _) -> embed r1 snd
  , getGen2 = \r1 r2 ->
     case r1 of
       RP _ r12 -> TSeq r12 (TSkip r1 r12 (P2 LR) snd) <$> getGen2 gId r12 r2
       _        -> comm r1 r2 snd
  }

gSplit :: forall a b c. (Typeable a, Typeable b, Typeable c)
       => a :=> b -> a :=> c -> a :=> (b, c)
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


gProd :: forall a b c d. (Typeable a, Typeable b, Typeable c, Typeable d)
      => a :=> b -> c :=> d -> (a, c) :=> (b, d)
gProd f g = gSplit (f . gFst) (g . gSnd)

instance Show a => Const a (:=>) where
  const x = lift (const x)

instance Arrow (:=>) where
  arr s f = lift (arr s f)
  fst = gFst
  snd = gSnd
  (***) = gProd
  (&&&) = gSplit

-- -- Sums:

gInl :: forall a b. (Typeable a, Typeable b)
     => a :=> Either a b
gInl
  = Gen
  { getGen1 = \r1 -> do
      let o = TL PType r1
      return $ DPair o (TSkip r1 o (S1 LR) inl)
  , getGen2 = \r1 r2 ->
      case eqR r1 r2 of
        Proved Refl -> return $ TSkip r1 r2 LR inl
        Disproved _ -> comm r1 r2 inl
  }

gInr :: forall a b. (Typeable a, Typeable b) => b :=> Either a b
gInr
  = Gen
  { getGen1 = \r1 -> do
      let o = TR PType r1
      return $ DPair o (TSkip r1 o (S2 LR) inr)
  , getGen2 = \r1 r2 -> do
      case eqR r1 r2 of
        Proved Refl -> return $ TSkip r1 r2 LR inr
        Disproved _ -> comm r1 r2 inr
  }

gCase :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => a :=> c -> b :=> c -> Either a b :=> c
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
           return $ DPair o1 (TBranchL r1 p1)

       TR _ l -> do
           DPair o1 p1 <- getGen1 g l
           return $ DPair o1 (TBranchR r1 p1)

       RI _ n -> do
           DPair o1 p1 <- getGen1 f (RI PType n)
           DPair o2 p2 <- getGen1 g (RI PType n)
           Join (o, g1, g2) <- rjoin o1 o2
           return $ DPair o $ TBranchI (TSeq o1 p1 g1) (TSeq o2 p2 g2)
  , getGen2 =  \r1 r2 ->
      case r1 of
       RS l r -> do
           p1 <- getGen2 f l r2
           p2 <- getGen2 g r r2
           return $ TBranchJ p1 p2
       TL _ l -> TBranchL r1 <$> getGen2 f l r2

       TR _ l -> TBranchR r1 <$> getGen2 g l r2

       RI _ n -> do
           p1 <- getGen2 f (RI PType n) r2
           p2 <- getGen2 g (RI PType n) r2
           return $ TBranchI p1 p2
  }

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
generate g = evalState (pgen >>= gen) ((S Z, Map.empty)::STR)
  where
    pgen    = getGen2 g ri ro
    ri = RI PType (sing :: Sing 'Z)
    ro = RI PType (sing :: Sing 'Z)

flatten :: RoleGen m => TRole -> m [Role]
flatten (RId   i) = return [Rol $ natToInt i]
flatten (RProd a b) = (++) <$> flatten a <*> flatten b
flatten (RSum r1 r2) = (:[]) <$> joinR r1 r2
flatten _ = error "Panic! Ill-formed protocol: Any can only occur \
                  \ as part of RSum"

getTypeOf :: forall t1 a. Typeable a => t1 ::: a -> TypeRep
getTypeOf _ = typeRep (Proxy :: Proxy a)

gen :: RoleGen m => r1 :==> r2 -> m Proto
gen (TComm ri ro f)
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
gen (TBranchI x1 x2) = genBranch x1 x2
gen (TBranchJ x1 x2) = genBranch x1 x2
gen (TBranchL _ x1) = gen x1
gen (TBranchR _ x1) = gen x1
gen (TSkip _ _ _ _) = pure GSkip

genBranch :: RoleGen m => r1 :==> r2 -> r3 :==> r4 -> m Proto
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
      = Choice i $ addAlt 0 (GComp Seq (msg i i1 r1) a)
                 $ addAlt 1 (GComp Seq (msg i i2 r2) b)
                 $ emptyAlt
    msg :: forall t a. Typeable a => Role -> [Role] -> t ::: a -> Proto
    msg f t pt
      | [f] == t = GSkip
      | otherwise = Comm $ Msg [f] t (Ty $ getTypeOf pt) (ECore (id :: a :-> a))

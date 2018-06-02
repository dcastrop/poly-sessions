{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
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

import Data.List ( nub )
import Data.Singletons
import Data.Singletons.Decide
import Data.Type.Natural
import Data.Typeable
import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Applicative ( (<|>) )
import Control.Constrained.Category
import Control.Constrained.Arrow
import Control.Monad.State.Strict hiding ( lift )
import Data.Text.Prettyprint.Doc ( Pretty(..) )

import Language.FPoly.Core
import Language.FPoly.Type
import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt, altMap )
import Language.SessionTypes.Global

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.

data TRole
  = RId Nat
  | RProd TRole TRole
  | RSumL TRole
  | RSumR TRole
  | RJoin TRole TRole
  deriving (Eq, Ord, Show)

instance Polynomial TRole where
  type (:*:) a b = 'RProd a b
  type (:+:) a b = 'RJoin ('RSumL a) ('RSumR b)

infixl 5 :\/:
type (:\/:) a b = 'RJoin a b

-- type family FstI (r :: TId) :: TId where
--   FstI ('TI n) = 'TI n
--   FstI ('TJ m r) = 'TJ (FstI m) (FstR r)

type family FstR (r :: TRole) :: TRole where
  FstR ('RId n) = 'RId n
  FstR ('RProd a _) = a
  FstR ('RJoin a b) = 'RJoin (FstR a) (FstR b)

type family SndR (r :: TRole) :: TRole where
  SndR ('RId n) = 'RId n
  SndR ('RProd _ b) = b
  SndR ('RJoin a b) = 'RJoin (SndR a) (SndR b)

infix 5 :::

data (:::) (t :: TRole) (a :: Type)  where
  RI :: PType t -> SNat n -> (:::) ('RId n) t
  RP :: (Typeable a, Typeable b) => (:::) r1 a -> (:::) r2 b -> (:::) ('RProd r1 r2) (a, b)
  RL ::(Typeable a, Typeable b) => PType b -> (:::) r1 a -> (:::) ('RSumL r1) (Either a b)
  RR ::(Typeable a, Typeable b) => PType a -> (:::) r1 b -> (:::) ('RSumR r1) (Either a b)
  RJ :: Typeable a => r1 ::: a -> r2 ::: a -> 'RJoin r1 r2  ::: a

fstR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> FstR r1 ::: a
fstR (RI _ n) = RI PType n
fstR (RP a _) = a
fstR (RJ a b) = RJ (fstR a) (fstR b)

sndR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> SndR r1 ::: b
sndR (RI _ n) = RI PType n
sndR (RP _ b) = b
sndR (RJ a b) = RJ (sndR a) (sndR b)

-- sndR (RS a b) = RS (sndR a) (sndR b)


infix 9 :<:

-- Less-than role relation. A value of this type is a "path" to r1 from r2, if
-- r1 :<: r2

data (:<:) :: TRole -> TRole -> Type where
  LR :: r :<: r
  LTrans :: r1 :<: r2 -> r2 :<: r3 -> r1 :<: r3
  P1 :: r1 :<: 'RProd r1 r2
  P2 :: r2 :<: 'RProd r1 r2
  S1 :: 'RSumL r0 :<: r0
  S2 :: 'RSumR r1 :<: r1
  J1 :: 'RJoin r r :<: r
  J2 :: r :<: 'RJoin r r
  -- (1 + 1) * (2 * 2) ~~~ (1 * 2 + 1 * 2) + (1 * 2 + 1 * 2)
  LD1 :: 'RJoin ('RProd a c) ('RProd b c) :<: 'RProd ('RJoin a b) c
  LD2 :: 'RJoin ('RProd a b) ('RProd a c) :<: 'RProd a ('RJoin b c)

  -- Congruence
  PC :: r1 :<: r3 -> r2 :<: r4 -> 'RProd r1 r2 :<: 'RProd r3 r4
  SC :: r1 :<: r3 -> r2 :<: r4 -> 'RJoin r1 r2 :<: 'RJoin r3 r4

ltFstR :: r1 ::: (a, b) -> FstR r1 :<: r1
ltFstR RI{} = LR
ltFstR RP{} = P1
ltFstR (RJ a b) = SC (ltFstR a) (ltFstR b)


ltSndR :: r1 ::: (a, b) -> SndR r1 :<: r1
ltSndR RI{} = LR
ltSndR RP{} = P2
ltSndR (RJ a b) = SC (ltSndR a) (ltSndR b)

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

  TAlt :: ri1 :==> ro1
       -> ri2 :==> ro2
       -> ri1 :\/: ri2 :==> ro1 :\/: ro2

  TBranchL :: ri1 :==> ro1
           -> 'RSumL ri1 :==> ro1

  TBranchR :: ri1 :==> ro1
           -> 'RSumR ri1 :==> ro1

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

  joinR :: TRole -> TRole -> m Role

type STR = (Nat, Map TRole Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (S r, m) >> return r
  keep c = get >>= \(i, _) -> c >>= \a -> get >>= \(_, m) -> put (i, m) >> return a
  joinR (RId n) (RId m)
    | n == m = return $ Rol $ natToInt n
  joinR (RSumL a) b = joinR a b
  joinR (RSumR a) b = joinR a b
  joinR a (RSumL b) = joinR a b
  joinR a (RSumR b) = joinR a b
  joinR a b = get >>= \(r, m) ->
      let rol = Rol $ natToInt r
          newm = Map.insert a rol $ Map.insert b rol m
      in maybe (put (S r, newm) *> return rol) return (lookupR m)
    where
      lookupR m = Map.lookup a m <|> Map.lookup b m

data ECore = forall a b. ECore (a :-> b)

instance Pretty ECore where
  pretty (ECore f) = pretty f

newtype Ty = Ty TypeRep

instance Pretty Ty where
  pretty (Ty t) = pretty $ show t

type Proto = GT String Ty ECore

data DPair b t1 where
  DPair :: forall b t1 t2. (:::) t2 b -> t1 :==> t2 -> DPair b t1

data (:=>) a b = Gen {
  getGen :: forall t1 m. (Typeable a, Typeable b, RoleGen m)
         =>  (:::) t1 a -> m (DPair b t1)
  }

withFreshId :: RoleGen m => (forall i. SNat i -> m b) -> m b
withFreshId f = fresh >>= \i -> withSomeSing i f

withNewRole :: RoleGen m => PType a -> (forall r. 'RId r ::: a -> m b) -> m b
withNewRole a f = withFreshId $ \i -> f (RI a i)

genFn :: (Typeable a, Typeable b)
      => (forall r1 m. RoleGen m => r1 ::: a -> m (DPair b r1)) -> a :=> b
genFn f = Gen $ \r ->
  case r of
--     RP (RJ a b) c -> do
--       let r' = (RJ (RP a c) (RP b c))
--       DPair o1 p1 <- getGen (genFn f) r'
--       return $ DPair o1 $ TSeq r' (TSkip r r' LD1 id) p1
--     RP a (RJ b c) -> do
--       let r' = (RJ (RP a b) (RP a c))
--       DPair o1 p1 <- getGen (genFn f) r'
--       return $ DPair o1 $ TSeq r' (TSkip r r' LD2 id) p1
    RJ a b -> do
      DPair o1 p1 <- keep $ getGen (genFn f) a
      DPair o2 p2 <- getGen (genFn f) b
      return $ DPair (RJ o1 o2) (TAlt p1 p2)
    _ -> f r

gId :: forall a. Typeable a => a :=> a
gId = genFn $ \r1 -> return $ DPair r1 $ TSkip r1 r1 LR id

gComp :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => b :=> c -> a :=> b -> a :=> c
gComp f g
  = genFn $ \r1 -> do
      DPair rt p1 <- getGen g r1
      DPair ro p2 <- getGen f rt
      return $ DPair ro $ TSeq rt p1 p2

instance Category (:=>) where
  type C (:=>) a = Typeable a
  id = gId
  (.) = gComp

wrap :: forall a b. (Typeable a, Typeable b) => a :-> b -> a :=> b
wrap f = genFn $ \ri -> withNewRole PType $ \ro -> return $ DPair ro $ TComm ri ro f

gFst :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> a
gFst = genFn $ \r1 -> do
  let r2 = fstR r1
  return $ DPair r2 $ TSkip r1 r2 (ltFstR r1) fst

gSnd :: forall a b. (Typeable a, Typeable b)
     => (a, b) :=> b
gSnd = genFn $ \r1 -> do
  let r2 = sndR r1
  return $ DPair r2 $ TSkip r1 r2 (ltSndR r1) snd

gSplit :: forall a b c. (Typeable a, Typeable b, Typeable c)
       => a :=> b -> a :=> c -> a :=> (b, c)
gSplit f g
  = genFn $ \r1 -> do
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
gInl = genFn $ \r1 -> do
         let o = RL PType r1
         return $ DPair o (TSkip r1 o S1 inl)

gInr :: forall a b. (Typeable a, Typeable b)
     => b :=> Either a b
gInr = genFn $ \r1 -> do
         let o = RR PType r1
         return $ DPair o (TSkip r1 o S2 inr)

ltSum :: SNat n -> ('RId n :+: 'RId n) :<: 'RId n
ltSum _ = LTrans (SC S1 S2) J1

gCase :: forall a b c. (Typeable a, Typeable b, Typeable c)
      => a :=> c -> b :=> c -> Either a b :=> c
gCase f g = genFn $ \ri ->
   case ri of
     RI _ n -> do
       let rl  = RI PType n
           rr  = RI PType n
           ri' = RJ (RL PType rl) (RR PType rr)
       DPair o p <- getGen (gCase f g) ri'
       return $ DPair o $ TSeq ri' (TSkip ri ri' (ltSum n) id) p

     RL PType r -> do
       DPair o p <- getGen f r
       return $ DPair o $ TBranchL p

     RR PType r -> do
       DPair o p <- getGen g r
       return $ DPair o $ TBranchR p

     RJ{} -> error "Panic! Impossible case"

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
generate g = evalState pcgen ((S Z, Map.empty)::STR)
  where
    pcgen    = do
      DPair _ p <- getGen g ri
      cgen p <*> pure GEnd
    ri = RI PType (sing :: SNat 'Z)

toSRole :: r ::: a -> TRole
toSRole (RI _ a) = RId $ fromSing a
toSRole (RJ a b) = RJoin (toSRole a) (toSRole b)
toSRole (RP a b) = RProd (toSRole a) (toSRole b)
toSRole (RL _ a) = RSumL (toSRole a)
toSRole (RR _ a) = RSumR (toSRole a)

flatten :: RoleGen m => TRole -> m [Role]
flatten (RId   i) = return [Rol $ natToInt i]
flatten (RProd a b) = (++) <$> flatten a <*> flatten b
flatten (RJoin r1 r2) = (:[]) <$> joinR r1 r2
flatten r = error $ "Panic! Ill-formed protocol: "
                  ++ show r
                  ++ " cannot occur during role flattening"

getTypeOf :: forall t1 a. Typeable a => t1 ::: a -> TypeRep
getTypeOf _ = typeRep (Proxy :: Proxy a)

step :: r1 :==> r2 -> Maybe (r1 :==> r2)
step (TSeq o1 (TSeq o2 x1 x2) x3)
  = Just (TSeq o2 x1 (TSeq o1 x2 x3))
step (TSeq (RJ o1 o2) (TAlt x1 x2) (TAlt x3 x4))
  = Just (TAlt (TSeq o1 x1 x3) (TSeq o2 x2 x4))
step (TSeq o (TBranchL x1) x2)
  = Just $ TBranchL (TSeq o x1 x2)
step (TSeq o (TBranchR x1) x2)
  = Just $ TBranchR (TSeq o x1 x2)
step (TSeq o x1 x2)
  | Just x1' <- step x1 = Just $ TSeq o x1' x2
  | Just x2' <- step x2 = Just $ TSeq o x1 x2'
--- I have to turn a r1 + r2 * r3 + r4 to (r1 * r3) + (r1 * r4) + ...
-- step (TSplit (TAlt x1 x2) (TAlt x3 x4))
--    = Just $
--        TAlt (TAlt (TSplit x1 x3) (TSplit x1 x4))
--             (TAlt (TSplit x2 x3) (TSplit x2 x4)
step (TSplit x1 x2)
  | Just x1' <- step x1 = Just $ TSplit x1' x2
  | Just x2' <- step x2 = Just $ TSplit x1 x2'
step (TAlt x1 x2)
  | Just x1' <- step x1 = Just $ TAlt x1' x2
  | Just x2' <- step x2 = Just $ TAlt x1 x2'
step (TBranchL x1)
  | Just x1' <- step x1 = Just $ TBranchL x1'
step (TBranchR x1)
  | Just x1' <- step x1 = Just $ TBranchR x1'
step _ = Nothing

getRoles :: Proto -> [Role]
getRoles (Choice r rs alts) = r:rs ++ concatMap getRoles lalts
  where
    lalts = map snd . Map.toList . altMap $ alts
getRoles (Comm (Msg r1 r2 _ _) c)= r1 ++ r2 ++ getRoles c
getRoles (GRec _ c) = getRoles c
getRoles _ = []

normalise :: r1 :==> r2 -> r1 :==> r2
normalise p | Just p' <- step p = go p'
            | otherwise = error "Nope"
  where
    go c | Just c' <- step c = go c'
         | otherwise = c

gen :: RoleGen m => r1 :==> r2 -> m (Proto -> Proto)
gen = cgen . normalise

cgen :: RoleGen m => r1 :==> r2 -> m (Proto -> Proto)
cgen (TComm ri ro f)
  = fmap Comm $
    Msg <$> flatten (toSRole ri)
        <*> flatten (toSRole ro)
        <*> pure (Ty $ getTypeOf ri)
        <*> pure (ECore f)
cgen (TDistr ri ro f)
  = fmap Comm $
    Msg <$> flatten (toSRole ri)
        <*> flatten (toSRole ro)
        <*> pure (Ty $ getTypeOf ri)
        <*> pure (ECore f)
cgen (TSplit x1 x2)
  = (.) <$> cgen x1 <*> cgen x2
cgen (TSeq o1 (TSeq o2 x1 x2) x3)
  = cgen $ TSeq o2 x1 (TSeq o1 x2 x3)
cgen (TSeq (RJ o1 o2) (TAlt x1 x2) (TAlt x3 x4))
  = cgen $ TAlt (TSeq o1 x1 x3) (TSeq o2 x2 x4)
cgen (TSeq o (TBranchL x) y) = cgen $ TBranchL (TSeq o x y)
cgen (TSeq o (TBranchR x) y) = cgen $ TBranchR (TSeq o x y)
cgen (TSeq _ x2 x3) = (.) <$> cgen x2 <*> cgen x3
--   where
--     go GSkip g = g
--     go g GSkip = g
--     go g1 g2   = GComp Seq g1 g2
cgen (TAlt x1 x2) = do
  a <- cgen x1
  b <- cgen x2
  t <- joinR t1 t2
  return $ \c ->
      let ac = a c
          bc = b c
          rs = filter (/= t) $ nub $ getRoles ac ++ getRoles bc
      in Choice t rs (addAlt 0 ac $ addAlt 1 bc emptyAlt)
  where
    t1 = inR x1
    t2 = inR x1
cgen (TBranchL x1) = cgen x1
cgen (TBranchR x1) = cgen x1
cgen TSkip{} = pure id

inR :: r1 :==> r2 -> TRole
inR (TComm r1 _ _) = toSRole r1
inR (TDistr r1 _ _) = toSRole r1
inR (TSplit r1 _) = inR r1
inR (TSeq _ r1 _) = inR r1
inR (TBranchL r1) = inR r1
inR (TBranchR r1) = inR r1
inR (TAlt r1 r2)
  = case (inR r1, inR r2) of
      (a, b) -> RJoin a b
inR (TSkip r _ _ _) = toSRole r

data AnyType where
  ATy :: Typeable a => PType a -> AnyType

rolety :: Typeable a => r1 ::: a -> PType a
rolety _ = PType

inTy :: r1 :==> r2 -> AnyType
inTy (TComm r1 _ _) = ATy (rolety r1)
inTy (TDistr r1 _ _) = ATy (rolety r1)
inTy (TSplit r1 _) = inTy r1
inTy (TSeq _ r1 _) = inTy r1
inTy (TAlt r1 _) = inTy r1
inTy (TBranchL r1) = inTy r1
inTy (TBranchR r1) = inTy r1
inTy (TSkip r _ _ _) = ATy (rolety r)

sumt :: PType a -> PType b -> PType (Either a b)
sumt PType PType = PType

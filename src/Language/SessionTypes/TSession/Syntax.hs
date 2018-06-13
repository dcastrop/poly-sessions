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
import Data.Singletons.TypeLits
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Num
import Data.Singletons.Prelude.Ord
import Data.Singletons.Prelude.Eq
import Data.Singletons.Decide
import Data.Typeable
import Data.Type.Mod
import Data.Type.Vector ( Vec )
import qualified Data.Type.Vector as V
import qualified Data.Map as Map
import Control.Applicative ( (<|>) )
import Control.Constrained.Category
import Control.Constrained.Arrow
import Control.Constrained.ArrowVector
import Control.Monad.State.Strict hiding ( lift )
import Data.Text.Prettyprint.Doc ( Pretty(..) )
import Numeric.Natural

import Unsafe.Coerce ( unsafeCoerce )

import Language.Poly.Core
import Language.Poly.Type
import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt, altMap )
import Language.SessionTypes.Global

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.

data TRole
  = RId Nat
  | RProd [TRole]
  | RSumL TRole
  | RSumR TRole
  | RJoin TRole TRole
  deriving (Eq, Ord)

data SRole
  = SId Natural
  | SProd [SRole]
  | SSumL SRole
  | SSumR SRole
  | SJoin SRole SRole
  deriving (Eq, Ord, Show)

instance Polynomial TRole where
  type (:*:) a b = 'RProd '[a, b]
  type (:+:) a b = 'RJoin ('RSumL a) ('RSumR b)

infixl 5 :\/:
type (:\/:) a b = 'RJoin a b

type family FstR (r :: TRole) :: TRole where
  FstR ('RId n) = 'RId n
  FstR ('RProd '[a, b]) = a
  FstR ('RJoin a b) = 'RJoin (FstR a) (FstR b)

type family SndR (r :: TRole) :: TRole where
  SndR ('RId n) = 'RId n
  SndR ('RProd '[a,b]) = b
  SndR ('RJoin a b) = 'RJoin (SndR a) (SndR b)

type family Proj (n :: Nat) (r :: TRole) :: TRole where
  Proj n ('RId m) = 'RId m
  Proj n ('RJoin a b) = 'RJoin (Proj n a) (Proj n b)
  Proj n ('RProd l) = l !! n

infix 5 :::

data (:::) (t :: TRole) (a :: Type)  where
  RI :: PType t
     -> SNat n
     -> (:::) ('RId n) t

  RP :: (Typeable a, Typeable b)
     => (:::) r1 a
     -> (:::) r2 b
     -> (:::) ('RProd '[r1, r2]) (a, b)

  RVZ :: (Typeable a)
      => (:::) ('RProd '[]) (Vec 0 a)

  RVS :: (Typeable a, Typeable n)
      => (:::) r1 a
      -> (:::) ('RProd r2) (Vec n a)
      -> (:::) ('RProd (r1 ': r2)) (Vec (1 + n) a)

  RL ::(Typeable a, Typeable b)
     => PType b
     -> (:::) r1 a
     -> (:::) ('RSumL r1) (Either a b)

  RR ::(Typeable a, Typeable b)
     => PType a
     -> (:::) r1 b
     -> (:::) ('RSumR r1) (Either a b)

  RJ :: Typeable a
     => r1 ::: a
     -> r2 ::: a
     -> 'RJoin r1 r2  ::: a

fstR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> FstR r1 ::: a
fstR (RI _ n) = RI PType n
fstR (RP a _) = a
fstR (RJ a b) = RJ (fstR a) (fstR b)

sndR :: (Typeable a, Typeable b) => r1 ::: (a,b) -> SndR r1 ::: b
sndR (RI _ n) = RI PType n
sndR (RP _ b) = b
sndR (RJ a b) = RJ (sndR a) (sndR b)

data IfZero n where
  IsZero :: IfZero n
  GtZero :: IfZero n

isZero :: KnownNat n => SNat n -> IfZero n
isZero n =
  case natVal n of
    0 -> IsZero
    _ -> GtZero

projR :: (Typeable a, KnownNat n)
      => SNat n -> r1 ::: Vec m a -> Proj n r1 ::: a
projR _ (RI _ n) = RI PType n
projR n (RJ a b) = RJ (projR n a) (projR n b)
projR n (RVS a b) =
  withKnownNat pn $
  case isZero n of
    IsZero -> unsafeCoerce $ a
    _      -> unsafeCoerce $ projR pn b
  where
    pn = n %- (sing :: SNat 1)
projR _ RVZ = error "Panic! impossible!"

-- sndR (RS a b) = RS (sndR a) (sndR b)


infix 9 :<:

-- Less-than role relation. A value of this type is a "path" to r1 from r2, if
-- r1 :<: r2

data (:<:) :: TRole -> TRole -> Type where
  LR :: r :<: r
  LTrans :: r1 :<: r2 -> r2 :<: r3 -> r1 :<: r3
  PR :: SNat n -> r1 :<: 'RProd rs -- XXX: No guarantees here!!
  S1 :: 'RSumL r0 :<: r0
  S2 :: 'RSumR r1 :<: r1
  J1 :: 'RJoin r r :<: r
  J2 :: r :<: 'RJoin r r
  -- (1 + 1) * (2 * 2) ~~~ (1 * 2 + 1 * 2) + (1 * 2 + 1 * 2)
  -- LD1 :: 'RJoin ('RProd a c) ('RProd b c) :<: 'RProd ('RJoin a b) c
  -- LD2 :: 'RJoin ('RProd a b) ('RProd a c) :<: 'RProd a ('RJoin b c)

  -- Congruence
  -- PC :: r1 :<: r3 -> r2 :<: r4 -> 'RProd r1 r2 :<: 'RProd r3 r4
  SC :: r1 :<: r3 -> r2 :<: r4 -> 'RJoin r1 r2 :<: 'RJoin r3 r4

ltFstR :: r1 ::: (a, b) -> FstR r1 :<: r1
ltFstR RI{} = LR
ltFstR RP{} = PR (sing :: SNat 0)
ltFstR (RJ a b) = SC (ltFstR a) (ltFstR b)

data EqRefl r where
  EqRefl :: (r == r) ~ 'True => EqRefl r

ltSndR :: r1 ::: (a, b) -> SndR r1 :<: r1
ltSndR RI{} = LR
ltSndR RP{} = PR (sing :: SNat 1)
ltSndR (RJ a b) = SC (ltSndR a) (ltSndR b)

--- XXX: wrong! n <= m
ltProjR :: KnownNat n => SNat n -> r1 ::: Vec m a -> Proj n r1 :<: r1
ltProjR _ RI{} = LR
ltProjR n (RVS _ b) =
  case isZero n of
    IsZero -> PR (sing :: SNat 0)
    _      -> case withKnownNat pn $ ltProjR pn b of
               PR t -> PR (t %+ (sing :: SNat 1))
               _    ->  error "Panic! Impossible"
  where
    pn = n %- (sing :: SNat 1)
ltProjR n (RJ a b) = SC (ltProjR n a) (ltProjR n b)
ltProjR _ RVZ = error "Panic! impossible!"

infixr 1 :==>

data LProc :: TRole -> [TRole] -> Type where
  LZ :: Typeable a => r1 ::: a -> LProc r1 '[]
  LS :: r1 :==> r2 -> LProc r1 rs -> LProc r1 (r2 ': rs)

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

  TSplit  :: LProc ri ro
          -> ri :==> 'RProd ro

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

class Monad m => RoleGen m where
  fresh :: m Natural
  keep  :: m a -> m a

  joinR :: SRole -> SRole -> m Role

type STR = (Natural, Map.Map SRole Role)

instance RoleGen (State STR) where
  fresh = get >>= \(r, m) -> put (r + 1, m) >> return r
  keep c = get >>= \(i, _) -> c >>= \a ->
             get >>= \(_, m) -> put (i, m) >> return a
  joinR (SId n) (SId m)
    | n == m = return $ Rol $ fromIntegral n
  joinR (SSumL a) b = joinR a b
  joinR (SSumR a) b = joinR a b
  joinR a (SSumL b) = joinR a b
  joinR a (SSumR b) = joinR a b
  joinR a b = get >>= \(r, m) ->
      let rol = Rol $ fromIntegral r
          newm = Map.insert a rol $ Map.insert b rol m
      in maybe (put (1 + r, newm) *> return rol) return (lookupR m)
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
         =>  (:::) t1 a -> m (DPair b t1) }

withFreshId :: RoleGen m => (forall i. SNat i -> m b) -> m b
withFreshId f = fresh >>= \i -> withSomeSing i f

withNewRole :: RoleGen m => PType a -> (forall r. 'RId r ::: a -> m b) -> m b
withNewRole a f = withFreshId $ \i -> f (RI a i)

genFn :: (Typeable a, Typeable b)
      => (forall r1 m. RoleGen m => r1 ::: a -> m (DPair b r1)) -> a :=> b
genFn f = Gen $ \r ->
  case r of
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
  type C (:=>) = Typeable
  id = gId
  (.) = gComp

tryReuse :: Bool -> RoleGen m => r ::: a -> m (SomeSing Nat)
tryReuse b (RI _ n) | b = toSing <$> fresh
                    | otherwise = pure $ SomeSing n
tryReuse _ (RP r1 _) = tryReuse False r1
tryReuse b (RJ r1 _) = tryReuse b r1
tryReuse _ RVZ = toSing <$> fresh
tryReuse _ (RVS r1 _) = tryReuse False r1
tryReuse b (RL _ r1) = tryReuse b r1
tryReuse b (RR _ r1) = tryReuse b r1

reuseRole :: forall a b r m t. (Typeable b, RoleGen m) => r ::: a -> (forall r'. r' ::: b -> m t) -> m t
reuseRole r f = tryReuse True r >>= \(SomeSing n) -> f (RI PType n)


wrap :: forall a b. (Typeable a, Typeable b) => a :-> b -> a :=> b
wrap f = genFn $ \ri -> reuseRole ri $ \ro ->
           return $ DPair ro $ TComm ri ro f

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
      return $ DPair (RP o1 o2) (TSplit $ LS p1 $ LS p2 $ LZ r1)

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

gGet :: forall a m. (Typeable a, KnownNat m)
     => TMod m -> Vec m a :=> a
gGet m =
  case modVal m of
    SomeSing i ->
      genFn $ \r1 ->  withKnownNat i $ do
        let r2 = projR i r1
        return $ DPair r2 $ TSkip r1 r2 (ltProjR i r1) (proj m)

data IsTypeable a where
  IsTypeable :: Typeable a => Proxy a -> IsTypeable a

data IsSing a where
  IsSing :: SingI a => Proxy a -> IsSing a

-- isTypeable :: SNat n -> IsTypeable n
-- isTypeable SZ = IsTypeable Proxy
-- isTypeable (SS n) = case isTypeable n of
                      -- IsTypeable Proxy -> IsTypeable Proxy
--
-- isSing :: SNat n -> IsSing n
-- isSing SZ = IsSing Proxy
-- isSing (SS n) = case isSing n of
                  -- IsSing Proxy -> IsSing Proxy

gVgen :: forall a b n. (Typeable a, Typeable b, KnownNat n)
     => (TMod n -> a :=> b) -> a :=> Vec n b
gVgen g = traverseIdx $ V.enum n
  where
    n = sing :: SNat n
    traverseIdx :: KnownNat c => Vec c (TMod n) -> a :=> Vec c b
    traverseIdx = V.foldr (\h t -> genFn $ \ri -> do
                              DPair ro1 p <- getGen (g h) ri
                              DPair ro2 (TSplit l) <- getGen t ri
                              return $ unsafeCoerce $ DPair (RVS ro1 ro2) $ TSplit $ LS p l)
                          (genFn $ \ri -> return $ unsafeCoerce $ DPair (RVZ :: 'RProd '[] ::: Vec 0 a) $ TSplit $ LZ ri)

instance ArrowVector Vec (:=>) where
  proj = gGet
  vec = gVgen

generate :: forall a b r. (Typeable a, Typeable b)
         => r ::: a ->  a :=> b -> Proto
generate ri g = evalState pcgen ((freshN ri, Map.empty)::STR)
  where
    pcgen    = do
      DPair _ p <- getGen g ri
      cgen p <*> pure GEnd

freshN :: r ::: a -> Natural
freshN (RI _ n) = 1 + fromIntegral (fromSing n)
freshN (RP a b) = 1 +  max (freshN a) (freshN b)
freshN RVZ{}    = 1
freshN (RVS a b) = 1 + max (freshN a) (freshN b)
freshN (RJ a b) = 1 + max (freshN a) (freshN b)
freshN (RL _ a) = 1 + freshN a
freshN (RR _ a) = 1 + freshN a

generateR :: forall a b. (Typeable a, Typeable b)
         => a :=> b -> Proto
generateR g = evalState pcgen ((1, Map.empty)::STR)
  where
    pcgen    = do
      DPair _ p <- getGen g ri
      cgen p <*> pure GEnd
    ri = RI PType (sing :: SNat 0)

toSRole :: r ::: a -> SRole
toSRole (RI _ a) = SId $ fromIntegral $ fromSing a
toSRole (RJ a b) = SJoin (toSRole a) (toSRole b)
toSRole (RP a b) = SProd [toSRole a, toSRole b ]
toSRole (RVZ   ) = SProd []
toSRole (RVS a b) | SProd l <- toSRole b = SProd (toSRole a : l)
                  | otherwise = error "Panic! Impossible"
toSRole (RL _ a) = SSumL (toSRole a)
toSRole (RR _ a) = SSumR (toSRole a)

flatten :: RoleGen m => SRole -> m [Role]
flatten (SId   i) = return [Rol $ fromIntegral i]
flatten (SProd a) = concat <$> mapM flatten a
flatten (SJoin r1 r2) = (:[]) <$> joinR r1 r2
flatten r = error $ "Panic! Ill-formed protocol: "
                  ++ show r
                  ++ " cannot occur during role flattening"

getTypeOf :: forall t1 a. Typeable a => t1 ::: a -> TypeRep
getTypeOf _ = typeRep (Proxy :: Proxy a)

stepL :: LProc r1 r2 -> Maybe (LProc r1 r2)
stepL (LS p1 p2) | Just p1' <- step p1 = Just $ LS p1' p2
stepL (LS p1 p2) | Just p2' <- stepL p2 = Just $ LS p1 p2'
stepL _ = Nothing

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
--- XXX: do I have to turn a r1 + r2 * r3 + r4 to (r1 * r3) + (r1 * r4) + ... ?
step (TSplit x1)
  | Just x1' <- stepL x1 = Just $ TSplit x1'
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

cgenL :: RoleGen m => LProc r1 r2 -> m (Proto -> Proto)
cgenL LZ{} = return id
cgenL (LS a b) = (.) <$> cgen a <*> cgenL b

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
cgen (TSplit x1)
  = cgenL x1
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

inRL :: LProc r1 ro -> SRole
inRL (LS r _) = inR r
inRL (LZ r) = toSRole r

inR :: r1 :==> r2 -> SRole
inR (TComm r1 _ _) = toSRole r1
inR (TDistr r1 _ _) = toSRole r1
inR (TSplit r1) = inRL r1
inR (TSeq _ r1 _) = inR r1
inR (TBranchL r1) = inR r1
inR (TBranchR r1) = inR r1
inR (TAlt r1 r2)
  = case (inR r1, inR r2) of
      (a, b) -> SJoin a b
inR (TSkip r _ _ _) = toSRole r

data AnyType where
  ATy :: Typeable a => PType a -> AnyType

rolety :: Typeable a => r1 ::: a -> PType a
rolety _ = PType

inTyL :: LProc r1 ro -> AnyType
inTyL (LS r _) = inTy r
inTyL (LZ r) = ATy $ rolety r

inTy :: r1 :==> r2 -> AnyType
inTy (TComm r1 _ _) = ATy (rolety r1)
inTy (TDistr r1 _ _) = ATy (rolety r1)
inTy (TSplit r1) = inTyL r1
inTy (TSeq _ r1 _) = inTy r1
inTy (TAlt r1 _) = inTy r1
inTy (TBranchL r1) = inTy r1
inTy (TBranchR r1) = inTy r1
inTy (TSkip r _ _ _) = ATy (rolety r)

sumt :: PType a -> PType b -> PType (Either a b)
sumt PType PType = PType

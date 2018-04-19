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

import Data.Kind hiding ( Type )

import Data.Singletons
import Control.Monad.State.Strict hiding ( lift )

import Language.Poly.C
import Language.Poly.Core hiding ( Nat, getType )
import Language.Poly.Type
-- import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt )
import Language.SessionTypes.Prefix.Global

data Idx = Z | S Idx

data instance Sing (t :: Idx) where
  SZ :: Sing 'Z
  SS :: Sing  n -> Sing ('S n)

type SIdx (t :: Idx) = Sing t

type SomeIdx = SomeSing Idx

instance SingI 'Z where
  sing = SZ
instance SingI n => SingI ('S n) where
  sing = SS sing

data SRole :: * -> * where
  SId   :: a -> SRole a
  SProd :: SRole a -> SRole a -> SRole a
  SSum  :: SRole a -> SRole a -> SRole a
  deriving (Eq, Ord)

-- | Type of roles: either a sum of roles, product of roles, or a constant
-- sometimes we do not know the other role in the sum of roles. For those cases,
-- we introduce 'TagL' and 'TagR'. We treat them as equal:
-- >>> SumR r1 r2 = TagL r1 = TagR r2.
data TRole :: * where
  RId   :: Type TyPrim -> Idx -> TRole
  RProd :: TRole -> TRole -> TRole
  RSum  :: TRole -> TRole -> TRole

infixl 6 :+:
infixl 7 :*:
infixl 9 :::

type (:*:) = 'RProd
type family (:+:) (l :: TRole) (r :: TRole) = (t :: TRole) | t -> l r where
  'RId a n :+: 'RId b n = 'RId ('TSum a b) n
  l        :+: r        = 'RSum l r

type family (:::) (r :: SRole Idx) (a :: Type TyPrim) = (s :: TRole) | s -> r a where
  'SId n ::: a = 'RId a n
  'SProd r s ::: 'TProd a b = 'RProd (r ::: a) (s ::: b)
  'SSum r s ::: 'TSum a b = 'RSum (r ::: a) (s ::: b)

-- -- | Singletonized role. Due to the use of Integers, I cannot derive these
-- -- using Data.Singletons.TH automatically
-- data instance Sing (t :: TRole) where
--   SRI :: Atom t -> Sing n -> Sing ('RId t n)
--   SRP :: Sing r1 -> Sing r2 -> Sing ('RProd r1 r2)
--   SRS :: Sing r1 -> Sing r2 -> Sing ('RSum r1 r2)
--   STL :: Sing r1 -> Sing ('RSum r1 r2)
--   STR :: Sing r2 -> Sing ('RSum r1 r2)

data STRole (a :: Type TyPrim) (t :: TRole) where
  RI :: SType t -> SIdx n                    -> STRole t            ('RId t n)
  RP :: STRole a r1 -> STRole b r2           -> STRole ('TProd a b) ('RProd r1 r2)
  RJ :: SType a -> STRole a r1 -> STRole a r2 -> STRole a            (r1 :+: r2)
  RS :: STRole a r1 -> STRole b r2           -> STRole ('TSum a b)  (r1 :+: r2)
  TL :: SType b -> STRole a r1               -> STRole ('TSum a b)  (r1 :+: r2)
  TR :: SType a -> STRole b r2               -> STRole ('TSum a b)  (r1 :+: r2)

class Monad m => RoleGen m where
   fresh :: m SomeIdx

type STR = SomeIdx

emptySTR :: STR
emptySTR = SomeSing SZ

instance RoleGen (State STR) where
  fresh = get >>= \r@(SomeSing i) ->
    put (SomeSing $ SS i) >> return r

-- instance SingKind TRole where
--   type DemoteRep TRole = SRole Integer
--
--   fromSing (RI _ n) = SId (fromSing n)
--   fromSing (RP a b) = SProd (fromSing a)  (fromSing b)
--   fromSing (RS a b) = SSum (fromSing a)  (fromSing b)
--   fromSing (RL a)   = SSum (fromSing a)  (fromSing b)
--
--   toSing _ = error "Cannot convert TRole to singleton type"
--
-- instance (SingI t, SingI n) => SingI ('RId t n) where
--   sing = RI sing sing
-- instance (SingI a, SingI b) => SingI ('RProd a b) where
--   sing = RP sing sing
-- instance (SingI a, SingI b) => SingI ('RSum a b) where
--   sing = RS sing sing
--
type family EraseR (r :: TRole) :: Type TyPrim where
  EraseR ('RId t _) = t
  EraseR ('RProd a b) = 'TProd (EraseR a) (EraseR b)
  EraseR ('RSum a b) = 'TSum (EraseR a) (EraseR b)

infix 9 :<:

data (:<:) :: TRole -> TRole -> * where
  LR :: r :<: r
  L1 :: r1 :<: r2 -> r1 :<: 'RProd r2 r3
  L2 :: r1 :<: r3 -> r1 :<: 'RProd r2 r3

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

  TBranch :: ri1 :==> ro
          -> ri2 :==> ro
          -> ri1 :+: ri2 :==> ro

  TBranchL :: ri1 :==> ro
           -> ri1 :+: ri2 :==> ro

  TBranchR :: ri2 :==> ro
           -> ri1 :+: ri2 :==> ro

  TSkip   :: STRole a ri
          -> ro :<: ri
          -> ri :==> ro

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
type (:=>) a b = forall t1 m. RoleGen m => STRole a t1 -> m (DPair b t1)

gId :: forall a. a :=> a
gId = \r1 -> pure $ DPair r1 (TSkip r1 LR)

gcomp :: forall a b c. b :=> c -> a :=> b -> a :=> c
gcomp f g = \r1 -> do
    DPair r2 p1 <- g r1
    DPair r3 p2 <- f r2
    return $ DPair r3 (TSeq r2 p1 p2)

-- Products

-- If we get a pair of roles, we just skip, with the left or right role as
-- output role.
-- If we get a single role, we lift the "fst" function
gfst :: forall a b. 'TProd a b :=> a
gfst = \r1 -> case r1 of
               RP p1 _ -> return $ DPair p1 (TSkip r1 (L1 LR))
               (RI (STProd a _) _) ->
                 do SomeSing i <- fresh
                    let r2 = RI a i
                    return $ DPair r2 (TComm r1 r2 Fst)
               (RJ (STProd a _) _ _) ->
                 do SomeSing i <- fresh
                    let r2 = RI a i
                    return $ DPair r2 (TComm r1 r2 Fst)

gsnd :: forall a b. 'TProd a b :=> b
gsnd = \r1 -> case r1 of
               RP _ p2 -> return $ DPair p2 (TSkip r1 (L2 LR))
               (RI (STProd _ a) _) ->
                 do SomeSing i <- fresh
                    let r2 = RI a i
                    return $ DPair r2 (TComm r1 r2 Snd)
               (RJ (STProd _ a) _ _) ->
                 do SomeSing i <- fresh
                    let r2 = RI a i
                    return $ DPair r2 (TComm r1 r2 Snd)

gsplit :: forall a b c. a :=> b -> a :=> c -> a :=> 'TProd b c
gsplit f g = \r1 -> do
   DPair o1 p1 <- f r1
   DPair o2 p2 <- g r1
   return $ DPair (RP o1 o2) (TSplit p1 p2)

gprod :: forall a b c d. a :=> b -> c :=> d -> 'TProd a c :=> 'TProd b d
gprod f g = gsplit (f `gcomp` gfst) (g `gcomp` gsnd)

extractTy :: STRole a t -> SType a
extractTy (RI t _) = t
extractTy (RJ t _ _) = t
extractTy (TL t r) = STSum (extractTy r) t
extractTy (TR t r) = STSum t (extractTy r)
extractTy (RS l r) = STSum (extractTy l) (extractTy r)
extractTy (RP l r) = STProd (extractTy l) (extractTy r)

joinRoles :: SType a -> STRole a t1 -> STRole a t2 -> STRole a (t1 :+: t2)
-- joinRoles t (TL r a) (TR l b) = RS a b
joinRoles r a        b        = RJ r a b

gcase :: forall a b c. a :=> c -> b :=> c -> 'TSum a b :=> c
gcase f g = \r1 ->
     case r1 of
       RI (STSum a b) n -> do
         DPair o1 p1 <- f $ RI a n
         DPair o2 p2 <- g $ RI b n
         let tc = extractTy o1
         let o = joinRoles tc o1 o2
         return $
           DPair o (TBranch (TSeq o1 p1 $ TComm o1 o Id)
                            (TSeq o2 p2 $ TComm o2 o Id))
       -- XXX: whenever we are treating the "join" of two roles, we should
       -- treat is as a new role identifier. However,
       RJ t _ _ -> do
         SomeSing i <- fresh
         let ri = RI t i
         DPair o p <- gcase f g ri
         return $ DPair o $ TSeq ri (TComm r1 ri Id) p
       TL _ l -> do
         DPair o p <- f l
         return $ DPair o (TBranchL p)
       TR _ l -> do
         DPair o p <- g l
         return $ DPair o (TBranchR p)
       RS l r -> do
         DPair o1 p1 <- f l
         DPair o2 p2 <- g r
         let tc = extractTy o1
         let o = joinRoles tc o1 o2
         let b1 = (TSeq o1 p1 $ TComm o1 o Id)
             b2 = (TSeq o2 p2 $ TComm o2 o Id)
         return $ DPair o $ TBranch b1 b2

ginl :: forall a b. SingI b => a :=> 'TSum a b
ginl = \r1 -> return $ DPair (TL sing r1) (TComm r1 (TL (sing :: Sing b) r1) Inl)

ginr :: forall a b. SingI a => b :=> 'TSum a b
ginr = \r1 -> return $ DPair (TR sing r1) (TComm r1 (TR (sing :: Sing a) r1) Inr)

-- ginlS :: forall e1 e2. Sing e1 -> Sing e2 -> (:==>) e1 ('RSum e1 e2)
-- ginlS e1 e2 = TComm e1 (RS e1 e2) Inl
--
-- ginrS :: forall e1 e2. Sing e1 -> Sing e2 -> (:==>) e2 ('RSum e1 e2)
-- ginrS e1 e2 = TComm e2 (RS e1 e2) Inr
--
-- gsum :: forall r1 r2 r3 r4.
--        (SingI r3, SingI r4)
--      => (:==>) r1 r3
--      -> (:==>) r2 r4
--      -> (:==>) ('RSum r1 r2) ('RSum r3 r4)
-- gsum f g = gcase (ginl `gcomp` f) (ginr `gcomp` g)
--
-- gsumS :: forall r1 r2 r3 r4.
--        Sing r3
--       -> Sing r4
--       -> (:==>) r1 r3
--       -> (:==>) r2 r4
--       -> (:==>) ('RSum r1 r2) ('RSum r3 r4)
-- gsumS r3 r4 f g = gcase (TSeq r3 f $ ginlS r3 r4)
--                         (TSeq r4 g $ ginrS r3 r4)
--
-- --- XXX: Functor refactor, combine with application in poly-lang
-- -- (maybe a typeclass?)
-- type RPoly = Poly TRole
--
-- type family (:@@:) (p :: RPoly) (t :: TRole) :: TRole where
--   'PK c :@@: t = c
--   'PId :@@: t = t
--   'PProd p1 p2 :@@: t = 'RProd (p1 :@@: t) (p2 :@@: t)
--   'PSum p1 p2 :@@: t = 'RSum (p1 :@@: t) (p2 :@@: t)
--
-- rapp :: forall (p :: RPoly) (t :: TRole).
--        Sing p -> Sing t -> Sing (p :@@: t)
-- rapp SPId           t = t
-- rapp (SPK c)       _t = c
-- rapp (SPProd p1 p2) t = RP (p1 `rapp` t) (p2 `rapp` t)
-- rapp (SPSum p1 p2)  t = RS (p1 `rapp` t) (p2 `rapp` t)
--
-- gfmap :: forall r1 r2 f. (SingI r1, SingI r2)
--       => Sing f
--       -> (:==>) r1 r2
--       -> (:==>) (f :@@: r1) (f :@@: r2)
-- gfmap (SPK r) _ = gidS r
-- gfmap SPId g = g
-- gfmap (SPProd p1 p2) f =
--   gprodS (rapp p1 (sing :: Sing r1)) (rapp p2 (sing :: Sing r1))
--          (gfmap p1 f) (gfmap p2 f)
-- gfmap (SPSum p1 p2) f =
--   gsumS (rapp p1 (sing :: Sing r2)) (rapp p2 (sing :: Sing r2))
--         (gfmap p1 f) (gfmap p2 f)
--
-- flatten :: forall (r :: TRole) m. RoleGen m => Sing r -> m [Role]
-- flatten (RI _ r) = return [Rol $ fromIntegral $ fromSing r]
-- flatten (RP r1 r2) = (++) <$> flatten r1 <*> flatten r2
-- flatten t@RS{} = (:[]) <$> fresh (fromSing t)
--
-- getType :: forall (r :: TRole). Sing r -> Sing (EraseR r)
-- getType (RI t _) = t
-- getType (RP r1 r2) = STProd (getType r1) (getType r2)
-- getType (RS r1 r2) = STSum (getType r1) (getType r2)
--
-- inR :: r1 :==> r2 -> Sing r1
-- inR (TComm ri _ _) = ri
-- inR (TSplit x1 _ ) = inR x1
-- inR (TSeq _ r _) = inR r
-- inR (TBranch x1 x2) = RS (inR x1) (inR x2)
-- inR (TSkip r _) = r
--
-- generate :: r1 :==> r2 -> Proto
-- generate g = evalState (gen g) emptySTR
--
-- gen :: RoleGen m => r1 :==> r2 -> m Proto
-- gen (TComm ri ro f) = fmap Comm $
--   Msg <$> flatten ri
--       <*> flatten ro
--       <*> pure (fromSing t1)
--       <*> pure (eraseTy (STArr t1 t2) f)
--   where
--     t1 = getType ri
--     t2 = getType ro
-- gen (TSplit x1 x2) = GComp Par <$> gen x1 <*> gen x2
-- gen (TSeq _ x2 x3) = GComp Seq <$> gen x2 <*> gen x3
-- gen (TBranch x1 x2)
--   = br <$> fresh r <*> flatten r1 <*> flatten r2 <*> gen x1 <*> gen x2
--   where
--     br i i1 i2 a b
--       = Choice i $ addAlt 0 (GComp Seq (msg i i1 $ getType r1) a)
--                  $ addAlt 1 (GComp Seq (msg i i2 $ getType r2) b)
--                  $ emptyAlt
--     msg f t pt = Comm $ Msg [f] t (fromSing pt) (eraseTy (STArr pt pt) Id)
--     r  = fromSing $ RS r1 r2
--     r1 = inR x1
--     r2 = inR x2
-- gen (TSkip _ _) = pure GSkip
--
-- --- XXX: refactor below to Combinators.hs
-- lift :: forall r1 r2.
--        (SingI r1, SingI r2)
--      => CCore (EraseR r1 ':-> EraseR r2)
--      -> (:==>) r1 r2
-- lift = TComm sing sing
--
-- type GenFn = forall s1 s2 a b r1 r2. (r1 ~ (s1 ::: a), r2 ~ (s2 ::: b))
--
-- data (:=>) :: Type TyPrim -> Type TyPrim -> * where
--   Gen :: (Sing r1 -> Sing r2 -> r1 ::: a :==> r2 ::: b) -> a :=> b
--

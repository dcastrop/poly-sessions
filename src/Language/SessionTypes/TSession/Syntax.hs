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
import Data.Singletons.TypeLits
import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Monad.State.Strict hiding ( lift )

import Language.Poly.C
import Language.Poly.Core hiding ( Nat, getType )
import Language.Poly.Type
import Language.SessionTypes.Common ( Role(..), addAlt, emptyAlt )
import Language.SessionTypes.Prefix.Global

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
  RId   :: Type TyPrim -> Nat -> TRole
  RProd :: TRole -> TRole -> TRole
  RSum  :: TRole -> TRole -> TRole

infixl 6 :+:
infixl 7 :*:
infixl 9 :~:
infixl 9 :::

type (:~:) = 'RId
type (:*:) = 'RProd
type (:+:) = 'RSum

type family (:::) (r :: SRole Nat) (a :: Type TyPrim) = (s :: TRole) | s -> r a where
  'SId n ::: a = 'RId a n
  'SProd r s ::: 'TProd a b = 'RProd (r ::: a) (s ::: b)
  'SSum r s ::: 'TSum a b = 'RSum (r ::: a) (s ::: b)

-- | Singletonized role. Due to the use of Integers, I cannot derive these
-- using Data.Singletons.TH automatically
data instance Sing (t :: TRole) where
  RI :: Sing t -> Sing n -> Sing ('RId t n)
  RP :: Sing r1 -> Sing r2 -> Sing ('RProd r1 r2)
  RS :: Sing r1 -> Sing r2 -> Sing ('RSum r1 r2)
  TL :: Sing r1 -> Sing ('RSum r1 r2)
  TR :: Sing r2 -> Sing ('RSum r1 r2)

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
  TComm  :: Sing ri
         -> Sing ro
         -> CCore (EraseR ri ':-> EraseR ro)
         -> ri :==> ro

  TSplit  :: ri :==> ro1
          -> ri :==> ro2
          -> ri :==> ro1 :*: ro2

  TSeq    :: Sing r
          -> ri :==> r
          -> r  :==> ro
          -> ri :==> ro

  TBranch :: ri1 :==> ro
          -> ri2 :==> ro
          -> ri1 :+: ri2 :==> ro

  TSkip   :: Sing ri
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

-- class Monad m => RoleGen m where
--    fresh :: SRole Integer -> m Role
--
-- type STR = (Int, Map (SRole Integer) Int)
--
-- emptySTR :: STR
-- emptySTR = (0, Map.empty)
--
-- instance RoleGen (State STR) where
--   fresh k = get >>= \(i, m) ->
--     case Map.lookup k m of
--       Just r -> return $ Rol r
--       Nothing -> do
--         put (i+1, Map.insert k i m)
--         return $ Rol i
--
-- type Proto = GT CType ECore
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
-- -- distrib :: forall r1 r2 a b. (SingI r1, SingI r2)
-- --         => CCore (a ':-> b)
-- --         -> (:==>) (r1 :~: a) (r2 ::: b)
-- -- distrib = TCommS sing sing
--
-- type GenFn = forall s1 s2 a b r1 r2. (r1 ~ (s1 ::: a), r2 ~ (s2 ::: b))
--
-- data (:=>) :: Type TyPrim -> Type TyPrim -> * where
--   Gen :: (Sing r1 -> Sing r2 -> r1 ::: a :==> r2 ::: b) -> a :=> b
--
-- gId :: forall a. a :=> a
-- gId = Gen $ \r1 r2 ->
--   case r1 %~ r2 of
--     Proved Refl -> TSkip sing LR
--     _           -> TComm (r1 %%% a) (r2 %%% a)
--
-- gid :: forall r. SingI r => r :==> r
-- gid = TSkip sing LR
--
-- gidS :: forall r. Sing r -> r :==> r
-- gidS r = TSkip r LR
--
-- gcomp :: forall r1 r2 r3. SingI r2 => r2 :==> r3 -> r1 :==> r2 -> r1 :==> r3
-- gcomp = flip $ TSeq sing
--
-- --- Products
-- gfstS :: forall r1 r2. Sing r1 -> Sing r2 -> r1 :*: r2 :==> r1
-- gfstS a b = TSkip (RP a b) (L1 LR)
--
-- gfst :: forall r1 r2. (SingI r1, SingI r2) => r1 :*: r2 :==> r1
-- gfst = gfstS sing sing
--
-- gsndS :: forall r1 r2. Sing r1 -> Sing r2 -> r1 :*: r2 :==> r2
-- gsndS a b = TSkip (RP a b) (L2 LR)
--
-- gsnd :: forall r1 r2. (SingI r1, SingI r2) => r1 :*: r2 :==> r2
-- gsnd = gsndS sing sing
--
-- gsplit :: forall r1 r2 r3. (:==>) r1 r2 -> (:==>) r1 r3
--        -> (:==>) r1 ('RProd r2 r3)
-- gsplit = TSplit
--
-- gprod :: forall r1 r2 r3 r4. (SingI r1, SingI r2)
--       => (:==>) r1 r3 -> (:==>) r2 r4
--       -> (:==>) ('RProd r1 r2) ('RProd r3 r4)
-- gprod = gprodS sing sing
--
-- gprodS :: forall r1 r2 r3 r4. Sing r1 -> Sing r2
--       -> (:==>) r1 r3 -> (:==>) r2 r4
--       -> (:==>) ('RProd r1 r2) ('RProd r3 r4)
-- gprodS r1 r2 f g = gsplit (TSeq r1 (gfstS r1 r2) f)
--                           (TSeq r2 (gsndS r1 r2) g)
--
-- gcase :: forall r1 r2 r3. (:==>) r1 r3 -> (:==>) r2 r3
--       -> (:==>) ('RSum r1 r2) r3
-- gcase = TBranch
--
-- -- Sums
-- ginl :: forall e1 e2. (SingI e1, SingI e2) => (:==>) e1 ('RSum e1 e2)
-- ginl = lift Inl
--
-- ginlS :: forall e1 e2. Sing e1 -> Sing e2 -> (:==>) e1 ('RSum e1 e2)
-- ginlS e1 e2 = TComm e1 (RS e1 e2) Inl
--
-- ginr :: forall e1 e2. (SingI e1, SingI e2) => (:==>) e2 ('RSum e1 e2)
-- ginr = lift Inr
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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.SessionTypes.RwSession
  ( Equiv(..)
  , Dir (..)
  , rwL, rwR
  , subst
  ) where

import qualified Data.Set as Set
import Control.Monad.Except
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Language.Poly.C
import Language.SessionTypes.Common
import Language.SessionTypes.RwError
import Language.SessionTypes.Prefix.Global
import Language.SessionTypes.Combinators

type RoleSpec =  [Role]

-- Substitute one rolename for another rolename in a global type.
-- Substitute a role by a pair of roles

subst :: MonadError Error m
      => RoleSpec
      -> Role
      -> Proto
      -> m Proto
subst [] _ _               = throwError EmptySubstitution
subst r1@[r] r2 (Choice f a)
  | f == r2                 = mChoice (return r) (substAlt r1 r2 a)
subst  r1  r2 (Choice f _a)
  | f == r2                 = throwError (MultiChoice r1 r2)
subst  r1  r2 (Choice f a) = mChoice (return f) (substAlt r1 r2 a)
subst  r1  r2 g@(NewRole r g1)
  | r == r2                 = return g
  | otherwise              = mNewRole (return r) (subst r1 r2 g1)
subst r1 r2 (GComp Par g1 g2)   = mGPar (subst r1 r2 g1) (subst r1 r2 g2)
subst r1 r2 (GComp Seq g1 g2)   = mGSeq (subst r1 r2 g1) (subst r1 r2 g2)
subst  r1  r2 (Comm    m)  = mComm (substMsg r1 r2 m)
subst _r1 _r2 t@GSkip      = return t

-- Substitute a role by a (pair of) role(s)
-- Invariant: types must match senders/receivers and operations
substMsg :: MonadError Error m
         => RoleSpec
         -> Role
         -> Msg CType ECore
         -> m (Msg CType ECore)
substMsg r1 r2 m = return m { rfrom = rf, rto = rt }
  where
    rtom  = rto m
    rfromm = rfrom m
    rt = F.concatMap (substRole r1 r2) rtom
    rf = F.concatMap (substRole r1 r2) rfromm

substAlt :: MonadError Error m
         => RoleSpec
         -> Role
         -> GBranch CType ECore
        -> m (GBranch CType ECore)
substAlt r1 r2 = T.mapM (subst r1 r2)

substRole :: RoleSpec -> Role -> Role -> RoleSpec
substRole r1 r2 r | r == r2    = r1
                   | otherwise = [r]

type RW t = t -> Maybe t

data Dir = L | R

data Equiv
  -- Equivalence
  = Refl | Sym Equiv | Trans Equiv Equiv

  -- Congruence
  | CChoice (Label ECore) Equiv
  | CNewRole Equiv
  | CPar Dir Equiv
  | CSeq Dir Equiv

  -- Rules
  | AssocPar | AssocSeq | SeqPar | CommutPar | DistParL
  | AssocParSeq | AssocSeqPar | SplitRecv Int | SplitSend Int
  | Hide Role | DistHide | AlphaConv Role
  | IdL | IdR | Bypass
  | CancelSplit | CancelAlt | SubstPar

rwL :: Equiv -> RW Proto
rwL Refl          = return
rwL (Sym r)       = rwR r
rwL (Trans e1 e2) = rwL e1 >=> rwL e2

rwL (CChoice l e) = \g ->
  case g of
    Choice r b -> fmap (Choice r) (adjust l (rwL e) b)
    _          -> Nothing

rwL (CNewRole e) = \g ->
  case g of
    NewRole r g1 -> fmap (NewRole r) (rwL e g1)
    _           -> Nothing

rwL (CPar d e) = \g ->
  case (g, d) of
    (GComp Par g1 g2, L)  -> fmap (flip (GComp Par) g2) $ rwL e g1
    (GComp Par g1 g2, R)  -> fmap (GComp Par g1) $ rwL e g2
    _           -> Nothing

rwL (CSeq d e) = \g ->
  case (g, d) of
    (GComp Seq g1 g2, L)  -> fmap (flip (GComp Seq) g2) $ rwL e g1
    (GComp Seq g1 g2, R)  -> fmap ((GComp Seq) g1) $ rwL e g2
    _           -> Nothing

rwL AssocPar = \g ->
  case g of
    (GComp Par g1 (GComp Par g2 g3)) -> Just ((g1 `gPar` g2) `gPar` g3)
    _                          -> Nothing

rwL AssocSeq = \g ->
  case g of
    (GComp Seq g1 (GComp Seq g2 g3))
      | fr g3 `Set.intersection` outr g1 `Set.intersection` inr g2
          `Set.isSubsetOf` outr g2,
        outr g1 `Set.intersection` outr g2 `Set.intersection` inr g3
        `Set.isSubsetOf` (inr g2 `Set.union` outr g3)
        -> Just ((g1 `gSeq` g2) `gSeq` g3)
    _ -> Nothing

rwL SeqPar = \g ->
  case g of
    GComp Seq g1 g2
      | outr g1 `Set.intersection` inr  g2 == Set.empty,
        outr g1 `Set.intersection` outr g2 == Set.empty
        -> Just $ g1 `gPar` g2
    _   -> Nothing

rwL CommutPar = \g ->
  case g of
    GComp Par g1 g2 -> Just $ g2 `gPar` g1
    _   -> Nothing

rwL DistParL = \g ->
  case g of
    GComp Seq g1 (GComp Par g2 g3)
      | inr g2 == inr g3, outr g1 `Set.difference` inr g2 == Set.empty
        -> Just $ (g1 `gSeq` g2) `gPar` g3
    _   -> Nothing

rwL AssocParSeq = \g ->
  case g of
    GComp Par g1 (GComp Seq g2 g3)
      | outr g1 `Set.intersection` outr g2 == Set.empty,
        outr g1 `Set.intersection` inr  g3 == Set.empty
        -> Just $ (g1 `gPar` g2) `gSeq` g3
    _   -> Nothing

rwL AssocSeqPar = \g ->
  case g of
    GComp Par (GComp Seq g1 g2) g3
      | outr g1 `Set.intersection` inr g3 == Set.empty
        -> Just $ g1 `gSeq` (g2 `gPar` g3)
    _   -> Nothing

rwL (SplitRecv k)= \g ->
  case g of
    Comm m
      | length (rto m) < k
        -> Just $ Comm m { rto = take k (rto m) } `gPar`
                 Comm m { rto = drop k (rto m) }
    _   -> Nothing

rwL (SplitSend k) = \g ->
  case g of
    Comm m
      | length (rfrom m) < k,
        Just (rty1, rty2) <- splitProd k (rty m)
        -> Just $ Comm m { rfrom = take k (rfrom m)
                        , msgAnn = EIdle
                        , rty = rty1 }
                `gSeq` Comm m { rfrom = drop k (rfrom m), rty = rty2 }
    _   -> Nothing
  where
    splitProd 1 (TProd t1 t2) = Just (t1, t2)
    splitProd n (TProd t1 t2)
      | n > 1, Just (t11, t12) <- splitProd (n-1) t2 = Just (TProd t1 t11, t12)
    splitProd _ _ = Nothing

rwL (Hide r) = \g ->
  if (r `Set.notMember` fr g)
  then Just $ NewRole r g
  else Nothing

rwL (AlphaConv r1) = \g1 ->
  case g1 of
    NewRole r2 g2
      | r1 `Set.notMember` fr g2
        -> fmap (NewRole r1) (subst [r1] r2 g2)
    _   -> Nothing

rwL DistHide = \g ->
  case g of
    NewRole r1 (GComp o g1 g2)
      -> Just $ GComp o (NewRole r1 g1) (NewRole r1 g2)
    _ -> Nothing

rwL IdL = \g ->
  case g of
    NewRole r (GComp Seq (Comm m1) g1)
      | Set.member r (inr g1)
      , rto m1 == [r]
      , isId (msgAnn m1)
      , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
        -> subst (rfrom m1) r g1
    _ -> Nothing

rwL IdR = \g ->
  case g of
    NewRole r (GComp Seq g1 (Comm m1))
      | Set.member r (outr g1)
      , rfrom m1 == [r]
      , isId (msgAnn m1)
      , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
        -> subst (rto m1) r g1
    _ -> Nothing

rwL Bypass = \g ->
  case g of
    NewRole r1 (NewRole r2 (GComp Seq (GComp Par g1 g2) (Comm m3)))
      | Set.toList (outr g1) == [r1]
      , Set.toList (outr g2) == [r2]
      , inr g1 == inr g2
      , rfrom m3 == [r1,r2]
      , Set.fromList (rto m3) `Set.intersection` fr g1 == Set.empty
      , Set.fromList (rto m3) `Set.intersection` fr g2 == Set.empty
      -> if isFst (msgAnn m3)
        then subst (rto m3) r1 g1
        else if isSnd (msgAnn m3)
             then subst (rto m3) r2 g2
             else Nothing
    _ -> Nothing

--  | CancelSplit | CancelAlt | SubstPar

rwL _ = const Nothing

rwR :: Equiv -> RW Proto
rwR Refl          = return
rwR (Sym r)       = rwL r
rwR (Trans e1 e2) = rwR e2 >=> rwR e1

rwR (CChoice l e) = \g ->
  case g of
    Choice r b -> fmap (Choice r) (adjust l (rwR e) b)
    _          -> Nothing

rwR (CNewRole e) = \g ->
  case g of
    NewRole r g1 -> fmap (NewRole r) (rwR e g1)
    _           -> Nothing

rwR (CPar d e) = \g ->
  case (g, d) of
    (GComp Par g1 g2, L)  -> fmap (flip (GComp Par) g2) $ rwR e g1
    (GComp Par g1 g2, R)  -> fmap (GComp Par g1) $ rwR e g2
    _           -> Nothing

rwR (CSeq d e) = \g ->
  case (g, d) of
    (GComp Seq g1 g2, L)  -> fmap (flip (GComp Seq) g2) $ rwR e g1
    (GComp Seq g1 g2, R)  -> fmap (GComp Seq g1) $ rwR e g2
    _           -> Nothing

rwR AssocPar = \g ->
  case g of
    (GComp Par (GComp Par g1 g2) g3) -> Just (g1 `gPar` (g2 `gPar` g3))
    _                          -> Nothing

rwR AssocSeq = \g ->
  case g of
    (GComp Seq (GComp Seq g1 g2) g3)
      | fr g3 `Set.intersection` outr g1 `Set.intersection` inr g2
          `Set.isSubsetOf` outr g2,
        outr g1 `Set.intersection` outr g2 `Set.intersection` inr g3
        `Set.isSubsetOf` (inr g2 `Set.union` outr g3)
        -> Just (g1 `gSeq` (g2 `gSeq` g3))
    _ -> Nothing

rwR SeqPar = \g ->
  case g of
    GComp Par g1 g2 -> Just $ g1 `gSeq` g2
    _            -> Nothing

rwR CommutPar = \g ->
  case g of
    GComp Par g1 g2 -> Just $ g2 `gPar` g1
    _   -> Nothing

rwR DistParL = \g ->
  case g of
    GComp Par (GComp Seq g1 g2) g3
      | inr g2 == inr g3, outr g1 `Set.difference` inr g2 == Set.empty
        -> Just $ g1 `gSeq` (g2 `gPar` g3)
    _   -> Nothing

rwR AssocParSeq = \g ->
  case g of
    GComp Seq (GComp Par g1 g2) g3
      | outr g1 `Set.intersection` outr g2 == Set.empty,
        outr g1 `Set.intersection` inr  g3 == Set.empty
        -> Just $ g1 `gPar` (g2 `gSeq` g3)
    _   -> Nothing

rwR (SplitRecv _)= \g ->
  case g of
    GComp Par (Comm m1) (Comm m2)
      | rfrom m1 == rfrom m2, rty m1 == rty m2, msgAnn m1 == msgAnn m2
        -> Just $ Comm $ m1 { rto = rto m1 ++ rto m2 }
    _   -> Nothing

rwR (SplitSend _) = \g ->
  case g of
    GComp Seq (Comm m1) (Comm m2)
      | rto m1 == rto m2, msgAnn m1 == EIdle
        -> Just $ Comm m1 { rfrom = rfrom m1 ++ rfrom m2
                         , rty = mkprod (rty m1) (rty m2)
                         }
    _   -> Nothing
  where
    mkprod (TProd t1 t2) t = TProd t1 (mkprod t2 t)
    mkprod t1 t2           = TProd t1 t2

rwR (Hide r) = \g ->
  case g of
    NewRole r1 g' | r == r1, r `Set.notMember` fr g -> Just g'
    _ -> Nothing

rwR (AlphaConv r1) = \g1 ->
  case g1 of
    NewRole r2 g2
      | r1 `Set.notMember` fr g2
        -> fmap (NewRole r1) (subst [r1] r2 g2)
    _   -> Nothing

rwR DistHide = \g ->
  case g of
    GComp o (NewRole r1 g1) (NewRole r2 g2)
      | r1 == r2 -> Just $ NewRole r1 (GComp o g1 g2)
    _ -> Nothing

-- TODO
--rwR IdL = \g ->
--rwR IdR = \g ->
--rwR BypassSplit = \g ->
--rwR SubstPar = \g ->

rwR _ = const Nothing

-- -- XXX REFACTOR
-- mergeRoles :: [Role] -> [Role] -> [Role]
-- mergeRoles r1 r2 = r1 ++ [r | r <- r2, r `notElem` r1]
--
-- rewrite :: (MonadError Error m, GenMonad Role m, MonadState [Role] m)
--         => ParSession -> m ParSession
-- rewrite = trans (congr step)
--
-- -- | Transitive closure
-- trans :: (MonadError Error m, GenMonad Role m, MonadState [Role] m)
--       => (ParSession -> m (Maybe ParSession))
--       -> ParSession -> m ParSession
-- trans rw p = do mp <- rw p
--                 case mp of
--                   Just p' -> trans rw p'
--                   Nothing -> return p
--
-- -- | Congruence rules
-- congr :: (MonadError Error m, GenMonad Role m, MonadState [Role] m)
--         => (ParSession -> m (Maybe ParSession))
--         -> ParSession
--         -> m (Maybe ParSession)
-- congr  rw g@(Choice  fr  tr  a1) =
--   do mg <- rw g
--      case mg of
--        Just _ -> return mg
--        Nothing ->
--          do ma <- congrAlt rw a1
--             case ma of
--               Nothing -> return Nothing
--               Just a2 ->
--                 do nr <- fmap (mergeRoles tr) get
--                    return $ Just $ Choice fr nr a2
-- congr  rw g@(Comm    m1  g1) =
--   do mg <- rw g
--      case mg of
--        Just _  -> return mg
--        Nothing -> fmap (fmap (Comm m1)) $ congr rw g1
-- congr  rw   (GRec    v1  g1)     = fmap (fmap (GRec v1)) $ congr rw g1
-- congr _rw   (GVar   _v1)         = return Nothing
-- congr _rw   GEnd                 = return Nothing
--
-- congrAlt :: (MonadError Error m, GenMonad Role m, MonadState [Role] m)
--         => (ParSession -> m (Maybe ParSession))
--         -> ParBranch
--         -> m (Maybe ParBranch)
-- congrAlt rw a = do ma <- T.traverse (congr rw) a
--                    return $ T.sequence ma
--
-- -- | The implementation of the core rules for rewriting a global type for
-- -- parallelism.
-- step :: (MonadError Error m, GenMonad Role m, MonadState [Role] m)
--      => ParSession
--      -> m (Maybe ParSession)
--
-- -- Rule: end-protocol
-- step (Comm msg@(msgAnn -> EEval _ Id) GEnd) =
--     return $ Just $ msg { msgAnn = EIdle } ... GEnd
--
-- -- Rule: short-circuit
-- -- m -> ws : A @ { id } . G
-- --    === G [ m / ws ]     <=== G /= end
-- step (Comm (Msg  rf  rt _pl (EEval (_t1 `STArr` _t1') Id)) cont) =
--     F.foldl' (\f x -> f <=< subst rf x) (return . Just) rt cont
--
-- -- Rule: pipeline
-- -- m -> ws : A @ { f . g } . G
-- --    === m -> w : A @ { f } . w -> ws : B @ { g } . G
-- step (Comm (Msg rf rt _pl (EEval (STArr _t1 _t3) (f `Comp` g))) cont) =
--   do w1    <- fresh "w"
--      State.modify' (w1:)
--      return $ Just $
--        Msg rf [w1] (fromSing (dom gty)) (EEval gty g)
--        ... Msg [w1] rt (fromSing (cod gty)) (EEval fty f)
--        ... cont
--   where
--     fty = typeOf f
--     gty = typeOf g
--
-- -- Rule: split
-- -- m -> {w1, ..., wn} : A @ {f /\ g}. G
-- --     ===   m -> {w11, ..., wn1} : A @ { f }
-- --         . m -> {w12, ..., wn2} : A @ { g }
-- --         . G [ w11 x w12 / w1, ..., wn1 x wn2 / wn ]
-- step (Comm (Msg rf rt pl (EEval _ty (f `Split` g))) cont) =
--   -- First split [rt]
--   do rt1 <- T.mapM (fresh . const "w") rt
--      rt2 <- T.mapM (fresh . const "w") rt
--      F.mapM_ (State.modify . (:)) $ rt1 ++ rt2
--   -- then congr each r \in rt into a pair of (r1,r2) with r1 \in rt1 and r2
--   -- \in rt2
--      cont' <- F.foldlM (\c (r1,r2) -> subst r1 r2 c) cont $
--                zip (zipWith (\a b -> [a,b]) rt1 rt2) rt
--      return $ Just $
--        Msg rf rt1 pl (EEval (typeOf f) f)
--        ... Msg rf rt2 pl (EEval (typeOf g) g)
--        ... cont'
--
-- -- Rule: case
-- -- m -> w* : A + B @ {f \/ g}. G
-- --     ===
-- --
-- --        m -> w* { 0: m -> w* : A @ {f}. G
-- --                , 1: m -> w* : B @ {g}. G
-- --                }
--
-- step (Comm (Msg rf@[r] rt _pl (EEval _ty (f `Case` g))) cont) =
--     return $ Just $
--       Choice r rt $
--         addAlt 0 EIdle (Comm (Msg rf rt plf (EEval dfty f)) cont) $
--         addAlt 1 EIdle (Comm (Msg rf rt plg (EEval dgty g)) cont) emptyAlt
--   where
--     plf = fromSing $ dom dfty
--     plg = fromSing $ dom dgty
--     dfty = typeOf f
--     dgty = typeOf g
--
-- step _x = return Nothing

isId :: ECore -> Bool
isId EIdle = True
isId (EEval _ Id) = True
isId _            = False

isFst :: ECore -> Bool
isFst (EEval _ Fst) = True
isFst _             = False

isSnd :: ECore -> Bool
isSnd (EEval _ Snd) = True
isSnd _            = False

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
module Language.SessionTypes.RwSession
  ( Equiv(..)
  , Dir (..)
  , rwL, rwR
  , subst
  , simplStep
  , simpl
  ) where

import Data.Text.Prettyprint.Doc ( Pretty, pretty )

import Data.Maybe ( catMaybes )
import Data.Map.Strict ( Map )
import qualified Data.Set as Set
import qualified Data.Map as Map
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
  deriving Show

simplStepAlts :: GBranch CType ECore -> [(Equiv, GBranch CType ECore)]
simplStepAlts b = concatMap simplStepAlt ks
  where
    m = altMap b
    ks = Map.keys m
    simplStepAlt k = map tag eqs
      where
        eqs = simplStep $ m Map.! k
        tag (e, g) = (CChoice k e, Alt $ Map.insert k g m)

simpl :: Proto -> [(Equiv, Proto)]
simpl p = case simplStep p of
            [] -> [(Refl, p)]
            l  -> concatMap go l
  where
    go (e, p') = map (\(e', p'') -> (trans e e', p'')) $ simpl p'
    trans Refl r = r
    trans r Refl = r
    trans r1 r2 = Trans r1 r2

simplStep :: Proto -> [(Equiv, Proto)]
simplStep (Choice f a) = map mkChoice $ simplStepAlts a
  where
    mkChoice (e, b) = (e, Choice f b)
simplStep t@(NewRole r g1) =
    map (\(rl, g1') -> (CNewRole rl, NewRole r g1')) (simplStep g1) ++
    (catMaybes $ fmap (Hide r,) (rwR (Hide r) t) :
                 map (\rl -> fmap (rl,) $ rwL rl t) allRules)
simplStep t@(GComp Par g1 g2) =
    catMaybes $ (map (\rl -> fmap ((CPar L rl,) . flip gPar g2) $ rwL rl g1) allRules)
                ++ map (\rl -> fmap ((CPar R rl,) . gPar g1) $ rwL rl g2) allRules
                ++ map (\rl -> fmap (rl,) $ rwL rl t) allRules
simplStep t@(GComp Seq g1 g2) =
    catMaybes $ (map (\rl -> fmap ((CPar L rl,) . flip gSeq g2) $ rwL rl g1) allRules)
                ++ map (\rl -> fmap ((CPar R rl,) . gSeq g1) $ rwL rl g2) allRules
                ++ map (\rl -> fmap (rl,) $ rwL rl t) allRules
simplStep _ = []

allRules :: [Equiv]
allRules = [ AssocPar, AssocSeq, SeqPar, CommutPar, DistParL, AssocParSeq
           , AssocSeqPar, SplitRecv 1, SplitSend 1, DistHide, CommutHide
           , IdL, IdR, Bypass, CancelSplit, CancelAlt ]

data Equiv
  -- Equivalence
  = Refl | Sym Equiv | Trans Equiv Equiv

  -- Congruence
  | CChoice (Label ECore) Equiv
  | CNewRole Equiv
  | CPar Dir Equiv
  | CSeq Dir Equiv
  | SubstPar Equiv

  -- Rules
  | AssocPar | AssocSeq | SeqPar | CommutPar | DistParL
  | AssocParSeq | AssocSeqPar | SplitRecv Int | SplitSend Int
  | Hide Role | DistHide | AlphaConv Role | CommutHide
  | IdL | IdR | Bypass
  | CancelSplit | CancelAlt
  deriving Show

instance Pretty Equiv where
  pretty = pretty . show

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
      | r1 `Set.notMember` (outr g1 `Set.union` inr g2)
      -> Just $ GComp o (NewRole r1 g1) (NewRole r1 g2)
    _ -> Nothing

rwL CommutHide = \g ->
  case g of
    NewRole r1 (NewRole r2 g') -> Just $ NewRole r2 (NewRole r1 g')
    _                         -> Nothing

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

rwL CancelSplit = \g ->
  case g of
    NewRole r1 (NewRole r2
                (GComp Seq (GComp Par (Comm m1) (Comm m2))
                (Comm m3)))
      | rfrom m1 == rfrom m2
      , rto m1 == [r1]
      , rto m2 == [r2]
      , rfrom m3 == [r1,r2] || rfrom m3 == [r2, r1]
      , isFst (msgAnn m1)
      , isSnd (msgAnn m2)
        -> Just $ Comm m3 { rfrom = rfrom m1 }
    _ -> Nothing

rwL CancelAlt = \g ->
  case g of
    GComp Seq (Comm m1) (Choice r br)
      | rto m1 == [r]
      , Just i <- isInj (msgAnn m1)
        -> fmap (GComp Seq (Comm m1 { msgAnn = EIdle })) (getAlt i br)
    _ -> Nothing

rwL (SubstPar e) =  \g ->
  case g of
    NewRole r (GComp Seq g1 (GComp Par g2 g3))
      | r `Set.member` outr g1
      , r `Set.member` inr g2
      , Just (GComp Seq g1' g2') <- rwL e (NewRole r $ GComp Seq g1 g2)
      , Just [(ra,r')] <- fmap (Map.toList . getSubst) $ alphaEquiv g1 g1'
      , ra == r
      , r' `Set.notMember` fr g3
      -> fmap (GComp Seq g1' . GComp Par g2') (subst [r'] r g3)
    _ -> Nothing

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
    NewRole r1 g' | r == r1, r `Set.notMember` fr g' -> Just g'
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

rwR CommutHide = \g ->
  case g of
    NewRole r1 (NewRole r2 g') -> Just $ NewRole r2 (NewRole r1 g')
    _                         -> Nothing

rwR _ = const Nothing

newtype AlphaEq = AlphaEq { getSubst :: Map Role Role }

alphaEquiv :: Proto -> Proto -> Maybe AlphaEq
alphaEquiv (Choice r1 br1) (Choice r2 br2)
  | Just s <- alphaBranch br1 br2
  = if r1 == r2 then Just s
    else do s' <- insertSubst (r1,r2) $ getSubst s
            return s { getSubst = s' }
alphaEquiv (Comm m1)       (Comm m2)       = alphaMsg m1 m2
alphaEquiv (NewRole r1 g1) (NewRole _ g2)
  | Just s <- alphaEquiv g1 g2
  = Just $ AlphaEq $ Map.delete r1 $ getSubst s
alphaEquiv (GComp o1 g11 g12) (GComp o2 g21 g22)
  | o1 == o2
  , Just s1 <- alphaEquiv g11 g21
  , Just s2 <- alphaEquiv g12 g22
  = fmap AlphaEq $ getSubst s1 `unionSubst` getSubst s2
alphaEquiv GSkip           GSkip           = Just $ AlphaEq Map.empty
alphaEquiv _               _               = Nothing

insertSubst :: (Role, Role) -> Map Role Role -> Maybe (Map Role Role)
insertSubst (r1, r2) m
  | Just r3 <- Map.lookup r1 m, r2 == r3 = Just m
  | Nothing <- Map.lookup r1 m          = Just $ Map.insert r1 r2 m
  | otherwise                          = Nothing

unionSubst :: Map Role Role -> Map Role Role -> Maybe (Map Role Role)
unionSubst m1 m2 = Map.foldlWithKey' add (Just m2) m1
    where
      add ms1 r1 r2 = ms1 >>= insertSubst (r1,r2)

alphaBranch :: GBranch CType ECore -> GBranch CType ECore -> Maybe AlphaEq
alphaBranch b1 b2 = go (altMap b1) (altMap b2)
  where
    go m1 m2
      | Map.size m1 == 0, Map.size m2 == 0 = Just $ AlphaEq Map.empty
      | Map.size m1 == 0  = Nothing
      | Map.size m2 == 0  = Nothing
      | otherwise
      = case Map.deleteFindMin m1 of
          ((lbl, g1), m1') ->
            do g1' <- Map.lookup lbl m2
               s1 <- alphaEquiv g1 g1'
               s2 <- go m1' (Map.delete lbl m2)
               fmap AlphaEq $ unionSubst (getSubst s1) (getSubst s2)

alphaMsg :: Msg CType ECore -> Msg CType ECore -> Maybe AlphaEq
alphaMsg m1 m2
  | rty m1 == rty m2, msgAnn m1 == msgAnn m2 =
      do s1 <- alphaRoles (rfrom m1) (rfrom m2)
         s2 <- alphaRoles (rto m1) (rto m2)
         fmap AlphaEq $ unionSubst s1 s2
  | otherwise = Nothing

alphaRoles :: [Role] -> [Role] -> Maybe (Map Role Role)
alphaRoles [] [] = Just Map.empty
alphaRoles (r1:rs1) (r2:rs2)
  | r1 == r2 = alphaRoles rs1 rs2
  | otherwise = alphaRoles rs1 rs2 >>= insertSubst (r1,r2)
alphaRoles _ _ = Nothing

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


isInj :: ECore -> Maybe Int
isInj (EEval _ Inl) = Just 1
isInj (EEval _ Inr) = Just 2
isInj _             = Nothing

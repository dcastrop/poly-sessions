{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}
module Language.SessionTypes.RwSession
where

import Data.Text.Prettyprint.Doc ( Pretty, pretty )

import Data.List ( elemIndex )
import Data.Map.Strict ( Map )
import qualified Data.Set as Set

import Control.Applicative
import Control.Arrow ( (&&&), (***) )
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import Language.Poly.C
import Language.Poly.UCore
import Language.Poly.Type
import Language.SessionTypes.Common
import Language.SessionTypes.Prefix.Global
import Language.SessionTypes.Combinators

type Subst = Map Role ([Role], Maybe ECore)

data Error
  = MultiChoice [Role] Role
  | InvalidSubst Role [Role]
  | CannotApply Rule (GT CType ECore)
  | EmptySubstitution
  | IllFormed (Msg CType ECore)
  | UnknownError

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty Error where
  pretty _ = pretty "there was an error"

-- Substitute one rolename for another rolename in a global type.
-- Substitute a role by a pair of roles

substr :: MonadError RwError m
       => (Role, Role)
       -> Proto
       -> m Proto
substr (r1,r2) = substRoleL r1 [r2] Nothing

substRoleL :: MonadError RwError m
           => Role -> [Role] -> Maybe ECore
           -> Proto
           -> m Proto
substRoleL r rs f = go
  where
    go (Choice rf a)
      | r == rf = case rs of
                   [r'] -> fmap (Choice r') $ goAlt a
                   _    -> throwError $ InvalidRw $ MultiChoice rs rf
      | otherwise = fmap (Choice rf) $ goAlt a
    go g@(NewRole nr g1)
      | r == nr = return g
      | otherwise = fmap (NewRole nr) $ go g1
    go (GComp o g1 g2) = liftM2 (GComp o) (go g1) (go g2)
    go (Comm m) = fmap Comm $ substMsgL r rs f m
    go t@GSkip  = return t

    goAlt = T.mapM go

substRole :: Role -> [Role] -> [Role] -> [Role]
substRole r1 rs r2 = concatMap subst r2
  where
    subst r | r1 ==  r = rs
            | otherwise = [r]

getTypes :: MonadError RwError m
         => Msg CType ECore -> [Role] -> CType -> m [CType]
getTypes _ [_] t = return [t]
getTypes m (_:xs) (TProd t1 t2) = fmap (t1:) $ getTypes m xs t2
getTypes m _ _ = throwError $ InvalidRw $ IllFormed m

-- FIXME: Very ugly, error-prone!! Revise substitution below!
substMsgL :: MonadError RwError m
          => Role -> [Role] -> Maybe ECore -> Msg CType ECore
          -> m (Msg CType ECore)
substMsgL r rs g m@Msg { rfrom = rf, rto = rt, rty = mty, msgAnn = f }
  | Just i <- r `elemIndex` rf, length rf > 1, length rs == 1
  = do tys <- getTypes m rf mty
       ntys <- fmap (F.foldr1 TProd) $ substType i tys
       let (ef : fs) = getFns i tys
       pr <- F.foldrM (fProd m) ef fs
       nf <- fComp m f pr
       return $ Msg { rfrom = substRole r rs rf
                    , rto = rt , rty = ntys , msgAnn = nf }
  | Just _ <- r `elemIndex` rf, length rf == 1, length rs >= 1
  = do [nty] <- substType 0 [mty]
       nf <- fComp m f $ getG g nty
       return $ Msg { rfrom = substRole r rs rf
                     , rto = rt , rty = nty , msgAnn = nf }
  | Just _ <- r `elemIndex` rt
  , (length rt == 1 && length rs >= 1) || (length rt > 1 && length rs == 1)
  = do b <- case ty f of
             _ :-> b -> return b
             _       -> throwError $ InvalidRw $ IllFormed m
       nf <- fComp m (getG g b) f
       return $ Msg { rfrom = rf
                    , rto =  substRole r rs rt
                    , rty = mty
                    , msgAnn = nf }
  | otherwise = throwError $ InvalidRw $ IllFormed m
  where
    substType n ts@(t:tsl) | n < 0 = return ts
                           | n == 0 = fmap (: tsl) $ msubst g t
                           | n > 0 = fmap (t :) $ substType (n-1) tsl
    substType _ _ = error "Panic! Impossible case"
    msubst Nothing t = return t
    msubst (Just e) _ = case ty e of
                          a :-> _ -> return a
                          _       -> throwError $ InvalidRw $ IllFormed m
    getFns n tys = zipWith mkF (take n tys) (repeat Id)
                 ++ (getG g (tys !! n)) :
                   zipWith mkF (drop (n+1) tys) (repeat Id)
    mkF t h = ECore (t :-> t) h
    getG Nothing t = ECore (t :-> t) Id
    getG (Just e) _ = e


fComp :: MonadError RwError m => Msg CType ECore -> ECore -> ECore -> m ECore
fComp _ (ECore (_ :-> b) f) (ECore (a :-> t) g)
  = return $ ECore (a :-> b) (comp t f g)
fComp m _ _ = throwError $ InvalidRw $ IllFormed m

fProd :: MonadError RwError m => Msg CType ECore -> ECore -> ECore -> m ECore
fProd _ (ECore (a :-> b) f) (ECore (c :-> d) g)
  = return $ ECore (TProd a c :-> TProd b d)
                   (split (comp a f Fst) (comp c g Snd))
fProd m _ _ = throwError $ InvalidRw $ IllFormed m

split :: UCCore -> UCCore -> UCCore
split Fst Snd = Id
split f g = Split f g

comp :: CType -> UCCore -> UCCore -> UCCore
comp _ Id f = f
comp _ f Id = f
comp a f g  = Comp a f g

type RW t = t -> Maybe t

data Dir = L | R
  deriving Show

-- A Script is a StateT
newtype Script m s a = Script { runScript :: s -> m (a, s) }

data RwError
  = NoRewrite | WrongPath Path Proto | NoOuterCtx Proto
  | InvalidRw Error | Unimplemented

instance Pretty RwError where
  pretty (InvalidRw err) = pretty err
  pretty (WrongPath d g) = pretty $ "Wrong path: " ++ (show d)
    ++ " " ++ (show $ pretty g)
  pretty _ = pretty "TODO: error-message pretty printing"

type RwErrorM m = MonadError RwError m

instance Monad m => Functor (Script m s) where
  fmap f s = Script $ \g -> runScript s g >>= return . (f *** id)

instance Monad m => Applicative (Script m s) where
  pure e = Script (return . (const e &&& id))
  af <*> ax = Script $ \g ->
    do (f, g') <- runScript af g
       (x, g'') <- runScript ax g'
       return (f x, g'')

instance RwErrorM m => Alternative (Script m s) where
  empty = Script $ const $ throwError NoRewrite
  s1 <|> s2 = Script $ \g ->
    catchError (runScript s1 g) $ \_ ->
      runScript s2 g

instance RwErrorM m => MonadError RwError (Script m s) where
  throwError e = Script $ const $ throwError e
  catchError (Script f) c = Script $ \g -> catchError (f g) $ \e ->
    runScript (c e) g

instance Monad m => Monad (Script m s) where
  return e = Script (return . (const e &&& id))
  s1 >>= ms2 = Script $ \g -> runScript s1 g >>= \(x, g') ->
    runScript (ms2 x) g'

instance Monad m => MonadState s (Script m s) where
  get = Script $ \g -> return (g, g)
  put ctx = Script $ const $ return ((), ctx)

data Context = Context { getCtx :: (Proto,[(Path, Proto)])
                       , freshGen :: Int }

collapse :: (Proto, [(Path, Proto)]) -> Proto
collapse (g, []) = g
collapse (g, t:ts) = collapse $ updateHead ts
  where
    updateHead [] = (update t g, [])
    updateHead ((d,g'):ts') = (g, (d, update t g') : ts')

current :: Context -> Proto
current Context{ getCtx = (g,[]) }         = g
current Context{ getCtx = (_, (_,g) : _) } = g

putCurrent :: Proto -> Context -> Context
putCurrent g c@Context{ getCtx = (_,[]) } = c { getCtx = (g,[]) }
putCurrent g c@Context{ getCtx = (gi, (d,_) : cs) }
  = c { getCtx =  (gi, (d,g) : cs) }

pushCtx :: (Path, Proto) -> Context -> Context
pushCtx t c@Context{ getCtx = (g, ts) } = c { getCtx = (g, t : ts) }

type RwScript m a = Script m Context a

fresh :: Monad m => (Int -> a) -> RwScript m a
fresh f = get >>= \ctx -> do
  let i = freshGen ctx
  put ctx { freshGen = i + 1 }
  return $ f i

getPath :: RwErrorM m => Path -> RwScript m Proto
getPath p = currentCtx >>= \g ->
  case (p, g) of
    (DChoice l, Choice _ br) ->
      maybe (throwError $ WrongPath p g) return (getAlt (labelId l) br)
    (DNewRole, NewRole _ g1)  -> return g1
    (DPar L, GComp Par g1 _2) -> return g1
    (DPar R, GComp Par _  g2) -> return g2
    (DSeq L, GComp Seq g1 _ ) -> return g1
    (DSeq R, GComp Seq _  g2) -> return g2
    _                         -> throwError $ WrongPath p g

currentCtx :: RwErrorM m => RwScript m Proto
currentCtx = fmap current get

putCtx :: RwErrorM m => Proto -> RwScript m ()
putCtx g = fmap (putCurrent g) get >>= put

update :: (Path, Proto) -> Proto -> Proto
update (DChoice l, g) (Choice r b) = Choice r $ addAlt (labelId l) g b
update (DNewRole, g) (NewRole r _) = NewRole r g
update (DPar L, g1) (GComp Par _ g2) = GComp Par g1 g2
update (DSeq L, g1) (GComp Seq _ g2) = GComp Par g1 g2
update (DPar R, g2) (GComp Par g1 _) = GComp Par g1 g2
update (DSeq R, g2) (GComp Seq g1 _) = GComp Par g1 g2
update _            _                =
  error "Panic! Inconsistent rewriting state!"

data Path
  = DChoice Label | DNewRole | DPar Dir | DSeq Dir
  deriving Show

rwAny :: RwErrorM m => [RwScript m a] -> RwScript m a
rwAny = F.asum

rwAll :: RwErrorM m => [RwScript m a] -> RwScript m [a]
rwAll = sequence

rwTrans :: RwErrorM m => [RwScript m Equiv] -> RwScript m Equiv
rwTrans = F.foldr (liftM2 trans) (return ERefl)
  where
    trans ERefl e = e
    trans e ERefl = e
    trans e1 e2 = Trans e1 e2


push :: RwErrorM m => Path -> RwScript m ()
push p = getPath p >>= \g -> modify $ pushCtx (p, g)

pop :: RwErrorM m => RwScript m ()
pop = get >>= \ctx ->
  case ctx of
    Context { getCtx = (gi, []) } -> throwError $ NoOuterCtx gi
    Context { getCtx = (gi, [t]) } -> put ctx { getCtx =  (update t gi, []) }
    Context { getCtx = (gi, t : (d, g) : cs) } ->
      put ctx { getCtx = (gi, (d, update t g) : cs) }

inPath :: RwErrorM m => Path -> RwScript m a -> RwScript m a
inPath p g = push p *> g <* pop

apply :: RwErrorM m => Rule -> RwScript m ()
apply r = currentCtx >>= \g -> rewrite r g >>= putCtx

ann :: Monad m => Equiv -> RwScript m a -> RwScript m Equiv
ann e g = g >> return e

try :: RwErrorM m => RwScript m a -> RwScript m a
try g = g
        <|> inPath DNewRole go
        <|> inPath (DPar L) go
        <|> inPath (DPar R) go
        <|> inPath (DSeq L) go
        <|> inPath (DSeq R) go
        <|> inPath (DChoice (Lbl 0)) go
        <|> inPath (DChoice (Lbl 1)) go
  where
    go = try g

tryAnn :: RwErrorM m => RwScript m Equiv -> RwScript m Equiv
tryAnn g = g
        <|> fmap CNewRole (inPath DNewRole go)
        <|> fmap (CPar L) (inPath (DPar L) go)
        <|> fmap (CPar R) (inPath (DPar R) go)
        <|> fmap (CSeq L) (inPath (DSeq L) go)
        <|> fmap (CSeq R) (inPath (DSeq R) go)
        <|> fmap (CChoice (Lbl 0)) (inPath (DChoice (Lbl 0)) go)
        <|> fmap (CChoice (Lbl 0)) (inPath (DChoice (Lbl 1)) go)
  where
    go = try g

data Rule
  = HideL | HideR | Hide | DistParSeq | CompL | CompR | Sym Rule
  deriving Show

rewrite :: RwErrorM m => Rule -> Proto -> RwScript m Proto
rewrite = rewriteL

rewriteL :: RwErrorM m => Rule -> Proto -> RwScript m Proto
rewriteL (Sym r) g = rewriteR r g

rewriteL HideL (GComp o (NewRole r1 g1) g2) = do
  r <- fresh Rol
  g1' <- substr (r1, r) g1
  return $ NewRole r $ GComp o g1' g2

rewriteL HideR (GComp o g1 (NewRole r1 g2)) = do
  r <- fresh Rol
  g2' <- substr (r1, r) g2
  return $ NewRole r $ GComp o g1 g2'

rewriteL Hide (NewRole r1 g)
  | r1 `Set.notMember` fr g
  = return g

rewriteL DistParSeq (GComp Par (GComp Seq g1 g2) (GComp Seq g3 g4))
  | outr g1 `Set.intersection` inr g4 == Set.empty
  , outr g3 `Set.intersection` inr g2 == Set.empty
  , outr g1 `Set.intersection` outr g3 == Set.empty
  = return $ GComp Seq (GComp Par g1 g3) (GComp Par g2 g4)

rewriteL CompL (NewRole r (GComp Seq (Comm m1) g1))
  | Set.member r (inr g1)
  , rto m1 == [r]
  , isPrim (msgAnn m1)
  , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
  = substRoleL r (rfrom m1) (Just $ msgAnn m1) g1

rewriteL CompR (NewRole r (GComp Seq  g1 (Comm m1)))
  | Set.member r (outr g1)
  , rfrom m1 == [r]
  , isPrim (msgAnn m1)
  , Set.fromList (rto m1) `Set.intersection` fr g1 == Set.empty
  = substRoleL r (rto m1) (Just $ msgAnn m1) g1

rewriteL r g
  = throwError $ InvalidRw $ CannotApply r g

rewriteR :: RwErrorM m => Rule -> Proto -> RwScript m Proto
rewriteR (Sym r) g = rewriteL r g

rewriteR HideL (NewRole r (GComp o g1 g2))
  | r `Set.notMember` fr g2
  = return $ GComp o (NewRole r g1) g2

rewriteR HideR (NewRole r (GComp o g1 g2))
  | r `Set.notMember` fr g1
  = return $ GComp o g1 (NewRole r g2)

rewriteR Hide g
  = do r <- fresh Rol
       return $ NewRole r g

rewriteR DistParSeq (GComp Seq (GComp Par g1 g3) (GComp Par g2 g4))
  | outr g1 `Set.intersection` inr g4 == Set.empty
  , outr g3 `Set.intersection` inr g2 == Set.empty
  , outr g1 `Set.intersection` outr g3 == Set.empty
  = return $ (GComp Par (GComp Seq g1 g2) (GComp Seq g3 g4))

rewriteR CompL _
  = throwError $ Unimplemented

rewriteR r g
  = throwError $ InvalidRw $ CannotApply (Sym r) g

type GScript a = RwScript (Either RwError) a

evalScript :: GScript a -> Proto -> Either RwError (a, Proto)
evalScript s g = either (Left . id) (Right . (id *** (collapse . getCtx))) $
  runScript s context
  where
    context = Context
      { getCtx = (g, [])
      , freshGen = head [n | n <- [0..], Rol n `Set.notMember` fr g ] }

testRule :: Rule -> Proto -> Either RwError Proto
testRule r g = either (Left . id) (Right . snd) $ evalScript (try $ apply r) g

many1 :: GScript Equiv -> GScript Equiv
many1 g = g >>= \e -> catchError (fmap (Trans e) $ many1 g) (\_ -> return e)

many0 :: GScript Equiv -> GScript Equiv
many0 g = catchError (many1 g) $ const $ return ERefl

stepScript :: GScript Equiv
stepScript =
  many0 $ tryAnn $
    (ann (Rule (Sym HideL)) $ apply $ Sym HideL)
  <|> (ann (Rule (Sym HideR)) $ apply $ Sym HideR)
  <|> (ann (Rule Hide) $ apply $ Hide)
  <|> (ann (Rule CompL) $ apply $ CompL)
  <|> (ann (Rule CompR) $ apply $ CompR)


step :: Proto -> Either RwError (Equiv, Proto)
step = evalScript stepScript

-- data Rule
--   = HideL | HideR | Hide | DistParSeq | CompL | CompR | Sym Rule

data Equiv
  -- Equivalence
  = ERefl | Trans Equiv Equiv

  -- Congruence
  | CChoice Label Equiv
  | CNewRole Equiv
  | CPar Dir Equiv
  | CSeq Dir Equiv
--  SubstPar Equiv

  -- Rules
  | Rule Rule
--   | AssocPar | AssocSeq | SeqPar | CommutPar | DistParL
--   | AssocParSeq | AssocSeqPar | SplitRecv Int | SplitSend Int
--   | Hide Role | DistHide | AlphaConv Role
--   | CommutHide
--   | IdL | IdR | Bypass
--   | CancelSplit | CancelAlt
  deriving Show

instance Pretty Equiv where
   pretty = pretty . show

-- simpl :: Proto -> [(Equiv, Proto)]
-- simpl p = aux (10 :: Int) p
--   where
--     go n (e, p') = map (\(e', p'') -> (trans e e', p'')) $ aux n p'
--     trans ERefl r = r
--     trans r ERefl = r
--     trans r1 r2 = Trans r1 r2
--     aux n pr
--       | n <= 0 = [(ERefl, pr)]
--       | otherwise = case simplStep rules pr of
--                       [] -> [(ERefl, pr)]
--                       l  -> concatMap (go $ n-1) l
--     rules = [ Sym HideL, Sym HideR
--             , Sym DistParSeq, CompL ]
--
-- simplStepAlts :: [Equiv] -> GBranch CType ECore -> [(Equiv, GBranch CType ECore)]
-- simplStepAlts rs b = concatMap simplStepAlt ks
--   where
--     m = altMap b
--     ks = Map.keys m
--     simplStepAlt k = map tag eqs
--       where
--         eqs = simplStep rs $ m Map.! k
--         tag (e, g) = (CChoice k e, Alt $ Map.insert k g m)
--
-- simplStep :: [Equiv] -> Proto -> [(Equiv, Proto)]
-- simplStep eq (Choice f a) = map mkChoice $ simplStepAlts eq a
--   where
--     mkChoice (e, b) = (e, Choice f b)
-- simplStep eq t@(NewRole r g1) =
--     map (\(rl, g1') -> (CNewRole rl, NewRole r g1')) (simplStep eq g1) ++
--     catMaybes (map (\rl -> fmap (rl,) $ rwL rl t) eq)
-- simplStep eq t@(GComp Par g1 g2) =
--     catMaybes $ map (\rl -> fmap ((CPar L rl,) . flip gPar g2) $ rwL rl g1) eq
--                 ++ map (\rl -> fmap ((CPar R rl,) . gPar g1) $ rwL rl g2) eq
--                 ++ map (\rl -> fmap (rl,) $ rwL rl t) eq
-- simplStep eq t@(GComp Seq g1 g2) =
--     catMaybes $ map (\rl -> fmap ((CSeq L rl,) . flip gSeq g2) $ rwL rl g1) eq
--                 ++ map (\rl -> fmap ((CSeq R rl,) . gSeq g1) $ rwL rl g2) eq
--                 ++ map (\rl -> fmap (rl,) $ rwL rl t) eq
-- simplStep _ _ = []
--
-- step :: Proto -> [(Equiv, Proto)]
-- step = simplStep allRules
--
-- allRules :: [Equiv]
-- allRules = [ HideL, HideR ]
-- -- SplitRecv 1, SplitSend 1, DistHide, Sym DistHide
-- --           , IdL, IdR, Bypass, CancelSplit, CancelAlt
-- --           , HideL, HideR
-- --           , SeqPar,  DistParL, AssocParSeq
-- --           , AssocSeqPar, AssocPar, AssocSeq, CommutPar, CommutHide ]
--
--
-- rwL :: Equiv -> RW Proto
-- rwL ERefl          = return
-- rwL (Sym r)       = rwR r
-- rwL (Trans e1 e2) = rwL e1 >=> rwL e2
--
-- rwL (CChoice l e) = \g ->
--   case g of
--     Choice r b -> fmap (Choice r) (adjust l (rwL e) b)
--     _          -> Nothing
--
-- rwL (CNewRole e) = \g ->
--   case g of
--     NewRole r g1 -> fmap (NewRole r) (rwL e g1)
--     _           -> Nothing
--
-- rwL (CPar d e) = \g ->
--   case (g, d) of
--     (GComp Par g1 g2, L)  -> fmap (flip (GComp Par) g2) $ rwL e g1
--     (GComp Par g1 g2, R)  -> fmap (GComp Par g1) $ rwL e g2
--     _           -> Nothing
--
-- rwL (CSeq d e) = \g ->
--   case (g, d) of
--     (GComp Seq g1 g2, L)  -> fmap (flip (GComp Seq) g2) $ rwL e g1
--     (GComp Seq g1 g2, R)  -> fmap ((GComp Seq) g1) $ rwL e g2
--     _           -> Nothing
--
-- rwL HideL = \g ->
--   case g of
--     GComp o t@(NewRole r1 g1) g2
--       -> let r = gen (fr t `Set.union` fr g2)
--         in fmap (NewRole r . flip (GComp o) g2) (substr (r1,r) g1)
--     _ -> Nothing
--
-- rwL HideR = \g ->
--   case g of
--     GComp o g1 t@(NewRole r1 g2)
--       -> let r = gen (fr t `Set.union` fr g1)
--         in fmap (NewRole r . GComp o g1) (substr (r1, r) g2)
--     _ -> Nothing
--
-- rwL (Hide r) = \g ->
--   case g of
--     NewRole r1 g' | r == r1, r `Set.notMember` fr g' -> Just g'
--     _ -> Nothing
--
-- rwL DistParSeq = \g ->
--   case g of
--     GComp Par (GComp Seq g1 g2) (GComp Seq g3 g4)
--       | outr g1 `Set.intersection` inr g4 == Set.empty
--       , outr g3 `Set.intersection` inr g2 == Set.empty
--       , outr g1 `Set.intersection` outr g3 == Set.empty
--         -> Just $ GComp Seq (GComp Par g1 g3)  (GComp Par g2 g4)
--     _   -> Nothing
--
-- rwL CompL = \g ->
--   case g of
--     NewRole r (GComp Seq (Comm m1) g1)
--       | Set.member r (inr g1)
--       , rto m1 == [r]
--       , isPrim (msgAnn m1)
--       , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
--         -> substrf (r, rfrom m1, msgAnn m1) g1
--     _ -> Nothing
--
-- -- rwL IdL = \g ->
-- --   case g of
-- --     NewRole r (GComp Seq (Comm m1) g1)
-- --       | Set.member r (inr g1)
-- --       , rto m1 == [r]
-- --       , isId (msgAnn m1)
-- --       , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
-- --         -> subst (rfrom m1) r g1
-- --     _ -> Nothing
-- --
-- -- rwL IdR = \g ->
-- --   case g of
-- --     NewRole r (GComp Seq g1 (Comm m1))
-- --       | Set.member r (outr g1)
-- --       , rfrom m1 == [r]
-- --       , isId (msgAnn m1)
-- --       , Set.fromList (rfrom m1) `Set.intersection` fr g1 == Set.empty
-- --         -> subst (rto m1) r g1
-- --     _ -> Nothing
-- --
-- -- rwL Bypass = \g ->
-- --   case g of
-- --     NewRole r1 (NewRole r2 (GComp Seq (GComp Par g1 g2) (Comm m3)))
-- --       | Set.toList (outr g1) == [r1]
-- --       , Set.toList (outr g2) == [r2]
-- --       , inr g1 == inr g2
-- --       , rfrom m3 == [r1,r2]
-- --       , Set.fromList (rto m3) `Set.intersection` fr g1 == Set.empty
-- --       , Set.fromList (rto m3) `Set.intersection` fr g2 == Set.empty
-- --       -> if isFst (msgAnn m3)
-- --         then subst (rto m3) r1 g1
-- --         else if isSnd (msgAnn m3)
-- --              then subst (rto m3) r2 g2
-- --              else Nothing
-- --     _ -> Nothing
-- --
-- -- rwL CancelSplit = \g ->
-- --   case g of
-- --     NewRole r1 (NewRole r2
-- --                 (GComp Seq (GComp Par (Comm m1) (Comm m2))
-- --                 (Comm m3)))
-- --       | rfrom m1 == rfrom m2
-- --       , rto m1 == [r1]
-- --       , rto m2 == [r2]
-- --       , rfrom m3 == [r1,r2] || rfrom m3 == [r2, r1]
-- --       , isFst (msgAnn m1)
-- --       , isSnd (msgAnn m2)
-- --         -> Just $ Comm m3 { rfrom = rfrom m1 }
-- --     _ -> Nothing
-- --
-- -- rwL CancelAlt = \g ->
-- --   case g of
-- --     GComp Seq (Comm m1) (Choice r br)
-- --       | rto m1 == [r]
-- --       , Just i <- isInj (msgAnn m1)
-- --         -> fmap (GComp Seq (Comm m1 { msgAnn = EIdle })) (getAlt i br)
-- --     _ -> Nothing
-- --
-- -- rwL AssocPar = \g ->
-- --   case g of
-- --     (GComp Par g1 (GComp Par g2 g3)) -> Just ((g1 `gPar` g2) `gPar` g3)
-- --     _                          -> Nothing
-- --
-- -- rwL AssocSeq = \g ->
-- --   case g of
-- --     (GComp Seq g1 (GComp Seq g2 g3))
-- --       | fr g3 `Set.intersection` outr g1 `Set.intersection` inr g2
-- --           `Set.isSubsetOf` outr g2,
-- --         outr g1 `Set.intersection` outr g2 `Set.intersection` inr g3
-- --         `Set.isSubsetOf` (inr g2 `Set.union` outr g3)
-- --         -> Just ((g1 `gSeq` g2) `gSeq` g3)
-- --     _ -> Nothing
-- --
-- -- rwL SeqPar = \g ->
-- --   case g of
-- --     GComp Seq g1 g2
-- --       | outr g1 `Set.intersection` inr  g2 == Set.empty,
-- --         outr g1 `Set.intersection` outr g2 == Set.empty
-- --         -> Just $ g1 `gPar` g2
-- --     _   -> Nothing
-- --
-- -- rwL CommutPar = \g ->
-- --   case g of
-- --     GComp Par g1 g2 -> Just $ g2 `gPar` g1
-- --     _   -> Nothing
-- --
-- -- rwL DistParL = \g ->
-- --   case g of
-- --     GComp Par (GComp Seq g1 g2) (GComp Seq g1' g3)
-- --       | Just s <- alphaEquiv g1 g1'
-- --       , Just g3' <- substs (Map.toList (getSubst s)) g3
-- --       , inr g2 == inr g3', outr g1 `Set.difference` inr g2 == Set.empty
-- --         -> Just $ g1 `gSeq` (g2 `gPar` g3')
-- --     _   -> Nothing
-- --   where
-- --     substs [] g = return g
-- --     substs ((r1,r2):s) g = subst [r1] r2 g >>= substs s
-- --
-- -- rwL AssocParSeq = \g ->
-- --   case g of
-- --     GComp Par g1 (GComp Seq g2 g3)
-- --       | outr g1 `Set.intersection` outr g2 == Set.empty,
-- --         outr g1 `Set.intersection` inr  g3 == Set.empty
-- --         -> Just $ (g1 `gPar` g2) `gSeq` g3
-- --     _   -> Nothing
-- --
-- -- rwL AssocSeqPar = \g ->
-- --   case g of
-- --     GComp Par (GComp Seq g1 g2) g3
-- --       | outr g1 `Set.intersection` inr g3 == Set.empty
-- --         -> Just $ g1 `gSeq` (g2 `gPar` g3)
-- --     _   -> Nothing
-- --
-- -- rwL (SplitRecv k)= \g ->
-- --   case g of
-- --     Comm m
-- --       | length (rto m) < k
-- --         -> Just $ Comm m { rto = take k (rto m) } `gPar`
-- --                  Comm m { rto = drop k (rto m) }
-- --     _   -> Nothing
-- --
-- -- rwL (SplitSend k) = \g ->
-- --   case g of
-- --     Comm m
-- --       | length (rfrom m) < k,
-- --         Just (rty1, rty2) <- splitProd k (rty m)
-- --         -> Just $ Comm m { rfrom = take k (rfrom m)
-- --                         , msgAnn = EIdle
-- --                         , rty = rty1 }
-- --                 `gSeq` Comm m { rfrom = drop k (rfrom m), rty = rty2 }
-- --     _   -> Nothing
-- --   where
-- --     splitProd 1 (TProd t1 t2) = Just (t1, t2)
-- --     splitProd n (TProd t1 t2)
-- --       | n > 1, Just (t11, t12) <- splitProd (n-1) t2 = Just (TProd t1 t11, t12)
-- --     splitProd _ _ = Nothing
-- --
-- -- rwL (AlphaConv r1) = \g1 ->
-- --   case g1 of
-- --     NewRole r2 g2
-- --       | r1 `Set.notMember` fr g2
-- --         -> fmap (NewRole r1) (subst [r1] r2 g2)
-- --     _   -> Nothing
-- --
-- -- rwL DistHide = \g ->
-- --   case g of
-- --     NewRole r1 (GComp o g1 g2)
-- --       | r1 `Set.notMember` (outr g1 `Set.union` inr g2)
-- --       -> Just $ GComp o (NewRole r1 g1) (NewRole r1 g2)
-- --     _ -> Nothing
-- --
-- -- rwL CommutHide = \g ->
-- --   case g of
-- --     NewRole r1 (NewRole r2 g') -> Just $ NewRole r2 (NewRole r1 g')
-- --     _                         -> Nothing
-- --
-- --
-- -- rwL (SubstPar e) =  \g ->
-- --   case g of
-- --     NewRole r (GComp Seq g1 (GComp Par g2 g3))
-- --       | r `Set.member` outr g1
-- --       , r `Set.member` inr g2
-- --       , Just (GComp Seq g1' g2') <- rwL e (NewRole r $ GComp Seq g1 g2)
-- --       , Just [(ra,r')] <- fmap (Map.toList . getSubst) $ alphaEquiv g1 g1'
-- --       , ra == r
-- --       , r' `Set.notMember` fr g3
-- --       -> fmap (GComp Seq g1' . GComp Par g2') (subst [r'] r g3)
-- --     _ -> Nothing
--
-- rwR :: Equiv -> RW Proto
-- rwR ERefl          = return
-- rwR (Sym r)       = rwL r
-- rwR (Trans e1 e2) = rwR e2 >=> rwR e1
--
-- rwR (CChoice l e) = \g ->
--   case g of
--     Choice r b -> fmap (Choice r) (adjust l (rwR e) b)
--     _          -> Nothing
--
-- rwR (CNewRole e) = \g ->
--   case g of
--     NewRole r g1 -> fmap (NewRole r) (rwR e g1)
--     _           -> Nothing
--
-- rwR (CPar d e) = \g ->
--   case (g, d) of
--     (GComp Par g1 g2, L)  -> fmap (flip (GComp Par) g2) $ rwR e g1
--     (GComp Par g1 g2, R)  -> fmap (GComp Par g1) $ rwR e g2
--     _           -> Nothing
--
-- rwR (CSeq d e) = \g ->
--   case (g, d) of
--     (GComp Seq g1 g2, L)  -> fmap (flip (GComp Seq) g2) $ rwR e g1
--     (GComp Seq g1 g2, R)  -> fmap (GComp Seq g1) $ rwR e g2
--     _           -> Nothing
--
-- rwR HideL = \g ->
--   case g of
--     NewRole r1 (GComp o g1 g2) | r1 `Set.notMember` fr g2
--       -> Just $ GComp o (NewRole r1 g1) g2
--     _ -> Nothing
--
-- rwR HideR = \g ->
--   case g of
--     NewRole r1 (GComp o g1 g2) | r1 `Set.notMember` fr g1
--       -> Just $ GComp o g1 (NewRole r1 g2)
--     _ -> Nothing
--
-- rwR (Hide r) = \g ->
--   if (r `Set.notMember` fr g)
--   then Just $ NewRole r g
--   else Nothing
--
-- rwR DistParSeq = \g ->
--   case g of
--     GComp Seq (GComp Par g1 g3)  (GComp Par g2 g4)
--       | outr g1 `Set.intersection` inr g4 == Set.empty
--       , outr g3 `Set.intersection` inr g2 == Set.empty
--       , outr g1 `Set.intersection` outr g3 == Set.empty
--         -> Just $ GComp Par (GComp Seq g1 g2) (GComp Seq g3 g4)
--     _   -> Nothing
--
-- --rwR AssocPar = \g ->
-- --  case g of
-- --    (GComp Par (GComp Par g1 g2) g3) -> Just (g1 `gPar` (g2 `gPar` g3))
-- --    _                          -> Nothing
-- --
-- --rwR AssocSeq = \g ->
-- --  case g of
-- --    (GComp Seq (GComp Seq g1 g2) g3)
-- --      | fr g3 `Set.intersection` outr g1 `Set.intersection` inr g2
-- --          `Set.isSubsetOf` outr g2,
-- --        outr g1 `Set.intersection` outr g2 `Set.intersection` inr g3
-- --        `Set.isSubsetOf` (inr g2 `Set.union` outr g3)
-- --        -> Just (g1 `gSeq` (g2 `gSeq` g3))
-- --    _ -> Nothing
-- --
-- --rwR SeqPar = \g ->
-- --  case g of
-- --    GComp Par g1 g2 -> Just $ g1 `gSeq` g2
-- --    _            -> Nothing
-- --
-- --rwR CommutPar = \g ->
-- --  case g of
-- --    GComp Par g1 g2 -> Just $ g2 `gPar` g1
-- --    _   -> Nothing
-- --
-- --rwR DistParL = \g ->
-- --  case g of
-- --    GComp Par (GComp Seq g1 g2) g3
-- --      | inr g2 == inr g3, outr g1 `Set.difference` inr g2 == Set.empty
-- --        -> Just $ g1 `gSeq` (g2 `gPar` g3)
-- --    _   -> Nothing
-- --
-- --rwR AssocParSeq = \g ->
-- --  case g of
-- --    GComp Seq (GComp Par g1 g2) g3
-- --      | outr g1 `Set.intersection` outr g2 == Set.empty,
-- --        outr g1 `Set.intersection` inr  g3 == Set.empty
-- --        -> Just $ g1 `gPar` (g2 `gSeq` g3)
-- --    _   -> Nothing
-- --
-- --rwR (SplitRecv _)= \g ->
-- --  case g of
-- --    GComp Par (Comm m1) (Comm m2)
-- --      | rfrom m1 == rfrom m2, rty m1 == rty m2, msgAnn m1 == msgAnn m2
-- --        -> Just $ Comm $ m1 { rto = rto m1 ++ rto m2 }
-- --    _   -> Nothing
-- --
-- --rwR (SplitSend _) = \g ->
-- --  case g of
-- --    GComp Seq (Comm m1) (Comm m2)
-- --      | rto m1 == rto m2, msgAnn m1 == EIdle
-- --        -> Just $ Comm m1 { rfrom = rfrom m1 ++ rfrom m2
-- --                         , rty = mkprod (rty m1) (rty m2)
-- --                         }
-- --    _   -> Nothing
-- --  where
-- --    mkprod (TProd t1 t2) t = TProd t1 (mkprod t2 t)
-- --    mkprod t1 t2           = TProd t1 t2
-- --
-- --
-- --rwR (AlphaConv r1) = \g1 ->
-- --  case g1 of
-- --    NewRole r2 g2
-- --      | r1 `Set.notMember` fr g2
-- --        -> fmap (NewRole r1) (subst [r1] r2 g2)
-- --    _   -> Nothing
-- --
-- --rwR DistHide = \g ->
-- --  case g of
-- --    GComp o (NewRole r1 g1) (NewRole r2 g2)
-- --      | r1 == r2
-- --        -> Just $ NewRole r1 (GComp o g1 g2)
-- --    GComp o (NewRole r1 g1) (NewRole r2 g2)
-- --      | r1 `Set.notMember` fr g2
-- --        -> fmap (NewRole r1 . GComp o g1) (subst [r1] r2 g2)
-- --    _   -> Nothing
-- --
-- --rwR CommutHide = \g ->
-- --  case g of
-- --    NewRole r1 (NewRole r2 g') -> Just $ NewRole r2 (NewRole r1 g')
-- --    _                         -> Nothing
-- --
-- --rwR _ = const Nothing
--
-- -- newtype AlphaEq = AlphaEq { getSubst :: Map Role Role }
-- --
-- -- alphaEquiv :: Proto -> Proto -> Maybe AlphaEq
-- -- alphaEquiv (Choice r1 br1) (Choice r2 br2)
--   -- | Just s <- alphaBranch br1 br2
--   -- = if r1 == r2 then Just s
--     -- else do s' <- insertSubst (r1,r2) $ getSubst s
--             -- return s { getSubst = s' }
-- -- alphaEquiv (Comm m1)       (Comm m2)       = alphaMsg m1 m2
-- -- alphaEquiv (NewRole r1 g1) (NewRole _ g2)
--   -- | Just s <- alphaEquiv g1 g2
--   -- = Just $ AlphaEq $ Map.delete r1 $ getSubst s
-- -- alphaEquiv (GComp o1 g11 g12) (GComp o2 g21 g22)
--   -- | o1 == o2
--   -- , Just s1 <- alphaEquiv g11 g21
--   -- , Just s2 <- alphaEquiv g12 g22
--   -- = fmap AlphaEq $ getSubst s1 `unionSubst` getSubst s2
-- -- alphaEquiv GSkip           GSkip           = Just $ AlphaEq Map.empty
-- -- alphaEquiv _               _               = Nothing
-- --
-- -- insertSubst :: (Role, Role) -> Map Role Role -> Maybe (Map Role Role)
-- -- insertSubst (r1, r2) m
--   -- | Just r3 <- Map.lookup r1 m, r2 == r3 = Just m
--   -- | Nothing <- Map.lookup r1 m          = Just $ Map.insert r1 r2 m
--   -- | otherwise                          = Nothing
-- --
-- -- unionSubst :: Map Role Role -> Map Role Role -> Maybe (Map Role Role)
-- -- unionSubst m1 m2 = Map.foldlWithKey' add (Just m2) m1
--     -- where
--       -- add ms1 r1 r2 = ms1 >>= insertSubst (r1,r2)
-- --
-- -- alphaBranch :: GBranch CType ECore -> GBranch CType ECore -> Maybe AlphaEq
-- -- alphaBranch b1 b2 = go (altMap b1) (altMap b2)
--   -- where
--     -- go m1 m2
--       -- | Map.size m1 == 0, Map.size m2 == 0 = Just $ AlphaEq Map.empty
--       -- | Map.size m1 == 0  = Nothing
--       -- | Map.size m2 == 0  = Nothing
--       -- | otherwise
--       -- = case Map.deleteFindMin m1 of
--           -- ((lbl, g1), m1') ->
--             -- do g1' <- Map.lookup lbl m2
--                -- s1 <- alphaEquiv g1 g1'
--                -- s2 <- go m1' (Map.delete lbl m2)
--                -- fmap AlphaEq $ unionSubst (getSubst s1) (getSubst s2)
-- --
-- -- alphaMsg :: Msg CType ECore -> Msg CType ECore -> Maybe AlphaEq
-- -- alphaMsg m1 m2
--   -- | rty m1 == rty m2, msgAnn m1 == msgAnn m2 =
--       -- do s1 <- alphaRoles (rfrom m1) (rfrom m2)
--          -- s2 <- alphaRoles (rto m1) (rto m2)
--          -- fmap AlphaEq $ unionSubst s1 s2
--   -- | otherwise = Nothing
-- --
-- -- alphaRoles :: [Role] -> [Role] -> Maybe (Map Role Role)
-- -- alphaRoles [] [] = Just Map.empty
-- -- alphaRoles (r1:rs1) (r2:rs2)
--   -- | r1 == r2 = alphaRoles rs1 rs2
--   -- | otherwise = alphaRoles rs1 rs2 >>= insertSubst (r1,r2)
-- -- alphaRoles _ _ = Nothing
-- --

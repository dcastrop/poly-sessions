{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
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
import qualified Data.Text.Prettyprint.Doc as Pretty

import Data.List ( elemIndex )
import Data.Map.Strict ( Map )
import Data.Monoid ( Monoid(..), (<>) )
import qualified Data.Set as Set

import Control.Applicative
import Control.Arrow ( (&&&), (***) )
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Extra
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
  | EmptySubstitution
  | IllFormed (Msg CType ECore) Role [Role]
  | IllTyped (Msg CType ECore)
  | UnknownError

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  pretty = either pretty pretty

instance Pretty Error where
  pretty (MultiChoice x1 x2) =
    Pretty.hsep
    [ pretty ("Substitution of" :: String)
    , pretty x2
    , pretty ("to " :: String)
    , pretty x1
    , pretty ("leads to ill-formed choice" :: String)
    ]
  pretty (InvalidSubst x1 x2) =
    Pretty.hsep
    [ pretty ("Invalid substitition of role" :: String)
    , pretty x1
    , pretty ("to " :: String)
    , pretty x2
    ]
  pretty EmptySubstitution =
    pretty ("Substitution leads to empty role sequence" :: String)
  pretty (IllFormed m r rs) = Pretty.vsep
    [ Pretty.hsep [ pretty ("Ill-formed message:" :: String)
                  , pretty m
                  ]
    , Pretty.hsep [ pretty ("after substitution of" :: String)
                  , pretty r
                  , pretty ("by" :: String)
                  , pretty rs ]
    ]
  pretty (IllTyped m) = Pretty.hsep [ pretty ("Ill-typed message:" :: String)
                                    , pretty m
                                    ]
  pretty UnknownError = pretty ("Unknown error" :: String)

-- Substitute one rolename for another rolename in a global type.
-- Substitute a role by a pair of roles

substr :: (MonadError RwError m, Alternative m)
       => (Role, Role)
       -> Proto
       -> m Proto
substr (r1,r2) = substRoleL r1 [r2] Nothing

substRoleL :: (MonadError RwError m, Alternative m)
           => Role -> [Role] -> Maybe ECore
           -> Proto
           -> m Proto
substRoleL r rs f = go
  where
    go (Choice rf a)
      | r == rf = case rs of
                   [r'] -> Choice r' <$> goAlt a
                   _    -> throwError $ InvalidRw $ MultiChoice rs r
      | otherwise = Choice rf <$> goAlt a
    go g@(NewRole nr g1)
      | r == nr = return g
      | otherwise = NewRole nr <$> go g1
    go (GComp o g1 g2) = GComp o <$> go g1 <*> go g2
    go (Comm m) = Comm <$> substMsgL r rs f m
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
getTypes m (_:xs) (TProd t1 t2) = (t1:) <$> getTypes m xs t2
getTypes m _ _ = throwError $ InvalidRw $ IllTyped m

-- FIXME: Very ugly, error-prone!! Revise substitution below!
substMsgL :: (MonadError RwError m, Alternative m)
          => Role -> [Role] -> Maybe ECore -> Msg CType ECore
          -> m (Msg CType ECore)
substMsgL r rs g m@Msg { rfrom = rf, rto = rt, rty = mty, msgAnn = f }
  | Just i <- r `elemIndex` rf, length rf > 1, length rs == 1
  = do tys <- getTypes m rf mty
       ntys <- F.foldr1 TProd <$> substType i tys
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
             _       -> throwError $ InvalidRw $ IllTyped m
       nf <- fComp m (getG g b) f
       return $ Msg { rfrom = rf
                    , rto =  substRole r rs rt
                    , rty = mty
                    , msgAnn = nf }
  | r `notElem` rf, r `notElem` rt
  = empty
  | otherwise = throwError $ InvalidRw $ IllFormed m r rs
  where
    substType n ts@(t:tsl) | n < 0 = return ts
                           | n == 0 = (: tsl) <$> msubst g t
                           | n > 0 = (t :) <$> substType (n-1) tsl
    substType _ _ = error "Panic! Impossible case"
    msubst Nothing t = return t
    msubst (Just e) _ = case ty e of
                          a :-> _ -> return a
                          _       -> throwError $ InvalidRw $ IllTyped m
    getFns n tys = zipWith mkF (take n tys) (repeat Id)
                 ++ (getG g (tys !! n)) :
                   zipWith mkF (drop (n+1) tys) (repeat Id)
    mkF t h = ECore (t :-> t) h
    getG Nothing t = ECore (t :-> t) Id
    getG (Just e) _ = e


fComp :: MonadError RwError m => Msg CType ECore -> ECore -> ECore -> m ECore
fComp _ (ECore (_ :-> b) f) (ECore (a :-> t) g)
  = return $ ECore (a :-> b) (comp t f g)
fComp m _ _ = throwError $ InvalidRw $ IllTyped m

fProd :: MonadError RwError m => Msg CType ECore -> ECore -> ECore -> m ECore
fProd _ (ECore (a :-> b) f) (ECore (c :-> d) g)
  = return $ ECore (TProd a c :-> TProd b d)
                   (split (comp a f Fst) (comp c g Snd))
fProd m _ _ = throwError $ InvalidRw $ IllTyped m

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

-- A Script is a 'kind-of' non-deterministic StateT
newtype Script m s a = Script { runScript :: s -> m [(a, s)] }

data RwError
  = WrongPath Path Proto
  | NoOuterCtx Proto
  | InvalidRw Error

instance Pretty RwError where
  pretty (NoOuterCtx g) =
    Pretty.hsep
    [ pretty ("Expression " :: String)
    , pretty g
    , pretty ("is already at the outermost level." :: String)]
  pretty (InvalidRw err) = pretty err
  pretty (WrongPath d g) = pretty $ "Wrong path: " ++ (show d)
    ++ " " ++ (show $ pretty g)

type RwErrorM m = MonadError RwError m

instance Monad m => Functor (Script m s) where
  fmap f s = Script $ \g -> runScript s g >>= return . fmap (f *** id)

instance Monad m => Applicative (Script m s) where
  pure e = Script (return . (:[]). (const e &&& id))
  af <*> ax = Script $ \g -> do
    l1 <- runScript af g
    concatMapM go l1
      where
        go (f, g) = map (f *** id) <$> runScript ax g

instance Monad m => Alternative (Script m s) where
  empty = Script $ const $ return []
  s1 <|> s2 = Script $ \g ->
    (++) <$> runScript s1 g <*> runScript s2 g

instance Monad m => Monoid (Script m s a) where
  mempty = empty
  s1 `mappend` s2 = Script $ \g -> do
  l1 <- runScript s1 g
  l2 <- runScript s2 g
  case l1 of
    [] -> return l2
    _  -> return l1

instance RwErrorM m => MonadError RwError (Script m s) where
  throwError e = Script $ const $ throwError e
  catchError (Script f) c = Script $ \g -> catchError (f g) $ \e ->
    runScript (c e) g

instance Monad m => Monad (Script m s) where
  return = pure
  s1 >>= ms2 = Script $ runScript s1 >=> concatMapM go
    where
      go (x, g') = runScript (ms2 x) g'

instance Monad m => MonadState s (Script m s) where
  get = Script $ \g -> return [(g, g)]
  put ctx = Script $ const $ return [((), ctx)]

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
      maybe empty return (getAlt (labelId l) br)
    (DNewRole, NewRole _ g1)  -> return g1
    (DPar L, GComp Par g1 _2) -> return g1
    (DPar R, GComp Par _  g2) -> return g2
    (DSeq L, GComp Seq g1 _ ) -> return g1
    (DSeq R, GComp Seq _  g2) -> return g2
    _                         -> empty

currentCtx :: RwErrorM m => RwScript m Proto
currentCtx = current <$> get

putCtx :: RwErrorM m => Proto -> RwScript m ()
putCtx g = putCurrent g <$> get >>= put

update :: (Path, Proto) -> Proto -> Proto
update (DChoice l, g) (Choice r b) = Choice r $ addAlt (labelId l) g b
update (DNewRole, g) (NewRole r _) = NewRole r g
update (DPar L, g1) (GComp Par _ g2) = GComp Par g1 g2
update (DSeq L, g1) (GComp Seq _ g2) = GComp Seq g1 g2
update (DPar R, g2) (GComp Par g1 _) = GComp Par g1 g2
update (DSeq R, g2) (GComp Seq g1 _) = GComp Seq g1 g2
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
    Context { getCtx = (g ,  []) } -> throwError $ NoOuterCtx g
    Context { getCtx = (gi, [t]) } -> put ctx { getCtx =  (update t gi, []) }
    Context { getCtx = (gi, t : (d, g) : cs) } ->
      put ctx { getCtx = (gi, (d, update t g) : cs) }

inPath :: RwErrorM m => Path -> RwScript m a -> RwScript m a
inPath p g = push p *> g <* pop

apply :: RwErrorM m => Rule -> RwScript m Equiv
apply r = currentCtx >>= \g -> rewrite r g >>= putCtx
  <?> const (Rule r)

infixr 0 <?>
(<?>) :: Monad m =>  RwScript m a -> (a -> b) -> RwScript m b
g <?> e = e <$> g


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

rewriteL _ _
  = empty

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

rewriteR _ _
  = empty

type GScript a = RwScript (Either RwError) a

evalScript :: GScript a -> Proto -> Either RwError [(a, Proto)]
evalScript s g = either Left (Right . map (id *** (collapse . getCtx))) $
  runScript s context
  where
    context = Context
      { getCtx = (g, [])
      , freshGen = head [n | n <- [0..], Rol n `Set.notMember` fr g ] }

testRule :: Rule -> Proto -> Either RwError [Proto]
testRule r g = either Left (Right . map snd) $ evalScript (congrRw $ apply r) g

many1 :: GScript Equiv -> GScript Equiv
many1 g = g >>= \e -> (many1 g <?> Trans e) <> pure e

many0 :: GScript Equiv -> GScript Equiv
many0 g = many1 g <> refl

refl :: RwErrorM m => RwScript m Equiv
refl = currentCtx <?> const ERefl

tryAll :: [Rule] -> GScript Equiv
tryAll = congrRw . F.asum .  map apply

tryAny :: [Rule] -> GScript Equiv
tryAny = congrRw . esum .  map apply

esum :: RwErrorM m => [RwScript m Equiv] -> RwScript m Equiv
esum = F.foldl' (<>) empty

congrRw :: RwErrorM m => RwScript m Equiv -> RwScript m Equiv
congrRw g = F.asum [g
  , inPath DNewRole          go <?> CNewRole
  , inPath (DPar L)          go <?> CPar L
  , inPath (DPar R)          go <?> CPar R
  , inPath (DSeq L)          go <?> CSeq L
  , inPath (DSeq R)          go <?> CSeq R
  , inPath (DChoice $ Lbl 0) go <?> CChoice (Lbl 0)
  , inPath (DChoice $ Lbl 1) go <?> CChoice (Lbl 1)
  ]
  where
    go = congrRw g

stepScript :: GScript Equiv
stepScript = tryAll
               [ HideL
               , HideR
               , Hide
               , CompL
               , CompR
               , DistParSeq
               ]

step :: Proto -> Either RwError [(Equiv, Proto)]
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

instance Pretty Equiv where
   pretty ERefl = pretty ("refl" :: String)
   pretty (Trans r1 r2) = Pretty.hsep [ pretty r1
                                      , pretty ("|>" :: String)
                                      , pretty r2 ]
   pretty (CChoice l e) = Pretty.hsep [ pretty l
                                      , pretty (":" :: String)
                                      , pretty e ]
   pretty (CNewRole e) = Pretty.hsep [pretty ("\\_" :: String), pretty e]
   pretty (CPar L e)
     =  Pretty.parens $ Pretty.hsep [pretty e, pretty ("|| _" :: String)]
   pretty (CPar R e)
     =  Pretty.parens $ Pretty.hsep [ pretty ("_ ||" :: String), pretty e]
   pretty (CSeq L e)
     =  Pretty.parens $ Pretty.hsep [pretty e, pretty (".. _" :: String)]
   pretty (CSeq R e)
     =  Pretty.parens $ Pretty.hsep [ pretty ("_ .." :: String), pretty e]
   pretty (Rule r)
     = pretty $ show r

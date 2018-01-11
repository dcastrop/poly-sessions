{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Language.SessionTypes.RwSession
  where
--  ( CCore
--  , ParSession
--  , RoleSpec (..)
--  , embed
--  , step
--  ) where

import Control.Monad ( (<=<) )
import Control.Monad.Except ( MonadError(..) )
import qualified Data.Traversable as T
import qualified Data.Foldable as F
import Data.Singletons

import Language.Internal.Id
import Language.SessionTypes.RwError
import Language.Poly.C
import Language.SessionTypes

-- []          m -> w : A { [] } . [
-- f : A -> B
type ParSession = GT Id CType ECore

class Monad m => GenMonad v m where
  fresh :: String -> m v

embed :: forall a b m. (SingI a, SingI b, GenMonad Role m)
      => CCore (a ':-> b) -> m ParSession
embed f =
    do m <- fresh "m"
       w <- fresh "w"
       return $
         Msg [m] [w] (fromSing t1) (EEval (t1 `STArr` t2) f)
         ... Msg [w] [m] (fromSing t2) EIdle
         ... GEnd
  where
    t1 :: Sing a
    t2 :: Sing b
    t1 = sing
    t2 = sing

type RoleSpec =  [Role]

-- Substitute one rolename for another rolename in a global type.
-- Substitute a role by a pair of roles
subst :: MonadError Error m
      => RoleSpec
      -> Role
      -> GT v CType ECore
      -> m (GT v CType ECore)
subst _r1 _r2 (Choice _f _t _a) = undefined
subst  r1  r2 (Comm    m  g)    = mComm (substMsg r1 r2 m) (subst r1 r2 g)
subst  r1  r2 (GRec    v  g)    = mGRec (return v) (subst r1 r2 g)
subst _r1 _r2 t@(GVar _g)       = return t
subst _r1 _r2 t@GEnd            = return t

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

substRole :: RoleSpec -> Role -> Role -> [Role]
substRole r1 r2 r | r == r2    = r1
                  | otherwise = [r]

step :: (MonadError Error m, GenMonad Role m) => ParSession -> m ParSession

-- Rule: end-protocol
step (Comm msg@(msgAnn -> EEval _ Id) GEnd) =
    return $ msg { msgAnn = EIdle } ... GEnd

-- Rule: short-circuit
-- m -> ws : A @ { id } . G
--    === G [ m / ws ]     <=== G /= end
step (Comm (Msg  rf  rt _pl (EEval (_t1 `STArr` _t1') Id)) cont) =
    F.foldl' (\f x -> f <=< subst rf x) return rt cont

-- Rule: pipeline
-- m -> ws : A @ { f . g } . G
--    === m -> w : A @ { f } . w -> ws : B @ { g } . G
step (Comm (Msg rf rt _pl (EEval (STArr _t1 _t3) (f `Comp` g))) cont) =
  do w1    <- fresh "w"
     return $
       Msg rf [w1] (fromSing (dom gty)) (EEval gty g)
       ... Msg [w1] rt (fromSing (cod gty)) (EEval fty f)
       ... cont
  where
    fty = typeOf f
    gty = typeOf g

-- Rule: split
-- m -> {w1, ..., wn} : A @ {f /\ g}. G
--     ===   m -> {w11, ..., wn1} : A @ { f }
--         . m -> {w12, ..., wn2} : A @ { g }
--         . G [ w11 x w12 / w1, ..., wn1 x wn2 / wn ]
step (Comm (Msg rf rt pl (EEval _ty (f `Split` g))) cont) =
  -- First split [rt]
  do rt1 <- T.mapM (fresh . const "w") rt
     rt2 <- T.mapM (fresh . const "w") rt
  -- then create sub-messages
     cont' <- F.foldlM (\c (r1,r2) -> subst r1 r2 c) cont $
               zip (zipWith (\a b -> [a,b]) rt1 rt2) rt
     return $
       Msg rf rt1 pl (EEval (typeOf f) f)
       ... Msg rf rt2 pl (EEval (typeOf g) g)
       ... cont'

-- --  FIXME: annotations not on every message, but on particular points:
-- --    r -> m : A . G puts a value of type 'A' in the context. The function in
-- --
-- --  In Haskell this corresponds to using a Maybe ann as annotation for Msg.
-- --
-- -- With choice, if there is a context T, a choice:
-- --
-- -- r -> m : { l1 : G1, ... ln : Gn} means that, at the beginning of Gi there
-- -- will be a value in a context of sum type  T_1 + ... + T_i-1 + T + T_i+1 + ...  -- + T_n
--
step x = return x

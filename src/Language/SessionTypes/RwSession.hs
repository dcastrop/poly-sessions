{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Language.SessionTypes.RwSession
( CCore
, ParSession
, RoleSpec (..)
, embed
, step
) where

import qualified Data.Set as Set
import Data.Singletons

import Language.Internal.Id
import Language.Poly.C
import Language.SessionTypes

-- []          m -> w : A { [] } . [
-- f : A -> B

type ParSession = GT Id (Type PrimTy) ECore

class Monad m => GenMonad m v where
  fresh :: String -> m v

embed :: forall a b m. (SingI a, SingI b, GenMonad m Role)
      => CCore (a ':-> b) -> m ParSession
embed f =
    do m <- fresh "m"
       w <- fresh "w"
       return $
         Msg m (Set.singleton w) (fromSing t1) (EEval (t1 `STArr` t2) f)
         ... Msg w (Set.singleton m) (fromSing t2) EEnd
         ... GEnd
  where
    t1 :: Sing a
    t2 :: Sing b
    t1 = sing
    t2 = sing

data RoleSpec = RK Role | RProd Role Role

-- Substitute one rolename for another rolename in a global type.
-- Substitute a role by a pair of roles
subst :: RoleSpec -> Role -> GT v t a  -> GT v t a
subst _r1 _r2 _g = undefined

step :: GenMonad m Role => ParSession -> m ParSession

-- Rule: end-protocol
step (Comm msg@(msgAnn -> EEval _ Id) GEnd) =
    return $ msg { msgAnn = EEnd } ... GEnd
step (Comm msg@(msgAnn -> EPush ) GEnd) =
    return $ msg { msgAnn = EEnd } ... GEnd

-- Rule: short-circuit
-- m -> ws : A @ { id } . G
--    === G [ m / ws ]     <=== G /= end
step   (Comm (Msg  rf  rt _pl (EEval (_t1 `STArr` _t1') Id)) cont) =
    return $ Set.foldl' (\f x -> f . subst (RK rf) x) id rt cont

-- m -> ws : A @ { f . g } . G
--    === m -> w : A @ { f } . w -> ws : B @ { g } . G
--
step (Comm (Msg rf rt _pl (EEval (STArr _t1 _t3) (f `Comp` g))) cont) =
  do w1 <- fresh "w"
     return $
       Msg rf (Set.singleton w1) (fromSing (dom fty)) (EEval fty f)
       ... Msg w1 rt (fromSing (cod fty)) (EEval gty g)
       ... cont
  where
    fty = typeOf f
    gty = typeOf g

-- m -> {w1, ..., wn} : A @ {f /\ g}. G
--     ===   m -> {w11, ..., wn1} : A @ { f }
--         . m -> {w12, ..., wn2} : A @ { g }
--         . G [ w11 x w12 / w1, ..., wn1 x wn2 / wn ]
--
--  where
--    (r -> r' : A x B @ { f }) [r1 x r2 / r] ~~~> r1 -> r' : A . r2 -> r' : B @ --    { f }
--     f (x,y) = ...
--
--  FIXME: annotations not on every message, but on particular points:
--    r -> m : A . G puts a value of type 'A' in the context. The function in
--
--  In Haskell this corresponds to using a Maybe ann as annotation for Msg.
--
-- With choice, if there is a context T, a choice:
--
-- r -> m : { l1 : G1, ... ln : Gn} means that, at the beginning of Gi there
-- will be a value in a context of sum type  T_1 + ... + T_i-1 + T + T_i+1 + ...  -- + T_n

step x = return x

{-
  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at https://mozilla.org/MPL/2.0/.
-}
{-# LANGUAGE CPP #-}

#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
{-# LANGUAGE NoStarIsType #-}
#endif
#endif

-- For multiplication
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Deep where

import Data (Norm (..), Vec, (:&:))
import Data.Constraint (Dict (..))
import Data.Constraint.Nat (Max, maxDistributesOverPlus, plusCommutes)
import Data.Set (Set)
import GHC.Base (Nat)
import GHC.TypeLits (type (+))
import GHC.TypeNats (type (-), type (<=))

--------------------------------------------------------------------------------

-- * A DSL for distance tracking

data Dist d a where
    -- Constant
    LInt :: Int -> Dist n Int
    -- Pairs under the L1 norm
    Pair ::
        (n ~ (nF + nS)) =>
        Dist nF a ->
        Dist nS b ->
        Dist n (a, b)
    -- Pairs under the LInf norm
    TPair ::
        -- The inequalities help, rather than derived them from Max
        (n ~ Max nS nF, nF <= n, nS <= n) =>
        Dist nF a ->
        Dist nS b ->
        Dist n (a :&: b)
    -- Vectors under the L1 norm (we can use the case of Haskell)
    DNil :: Dist n (Vec 'L1 0 a)
    DCons ::
        (n ~ (nH + nT)) =>
        Dist nH a ->
        Dist nT (Vec 'L1 m a) ->
        Dist n (Vec 'L1 (m + 1) a)
    -- Vectors under the LInf norm
    TNil :: Dist n (Vec 'LInf 0 a)
    TCons ::
        (n ~ Max nH nT) =>
        Dist nH a ->
        Dist nT (Vec 'LInf m a) ->
        Dist n (Vec 'LInf (m + 1) a)
    -- Finite sets
    DSet :: Set a -> Dist n (Set a)

--------------------------------------------------------------------------------

-- * Operations on distances

-- | Increase the distance of an expression by adding a constant
up :: forall c n a. Dist n a -> Dist (n + c) a
up (LInt r) = LInt r
up (DSet s) = DSet s
up (Pair x y) = Pair (up x) y
up DNil = DNil
up (DCons x xs) = DCons (up x) xs
up TNil = TNil
up (TCons (x :: Dist nH z) (xs :: Dist nT (Vec 'LInf m z))) =
    case (proof, p1, p2, p3) of
        (Dict, Dict, Dict, Dict) -> TCons x' xs'
  where
    proof = maxDistributesOverPlus @c @nH @nT
    p1 = plusCommutes @c @(Max nH nT)
    p2 = plusCommutes @c @nH
    p3 = plusCommutes @c @nT
    x' = up @c x
    xs' = up @c xs
up (TPair x y) = TPair x' y'
  where
    x' = up @c (up2 @n x)
    y' = up @c (up2 @n y)

-- | Increase the distance of an expression to an upper bound
up2 :: forall m' n a. (n <= m') => Dist n a -> Dist m' a
up2 = up @(m' - n)

--------------------------------------------------------------------------------

-- * The privacy monad

-- | Privacy monad parameterized by the privacy level e
newtype PM (e :: Nat) a = PM (IO a)

-- | Return function for the privacy monad
dpReturn :: a -> PM 0 a
dpReturn = PM . return

-- | Bind operator for the privacy monad
dpBind :: PM e a -> (a -> PM e' b) -> PM (e + e') b
dpBind (PM ioa) f = PM $ do
    a <- ioa
    let (PM iob) = f a
    iob

-- | Lift an IO action to the privacy monad
dpLift :: IO a -> PM e a
dpLift = PM

-- | Functor instance for the privacy monad
instance Functor (PM e) where
    fmap f (PM io) = PM (fmap f io)

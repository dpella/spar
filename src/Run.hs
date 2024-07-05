{-
  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at https://mozilla.org/MPL/2.0/.
-}
module Run where

import Data (Norm (..), Vec (..), type (:&:) (..))
import Data.Set (Set)
import Deep (Dist (..))

-- | Reflection and reification: from Haskell @a@ type to relational @Dist n a@
-- and from @Dist n a@ to @a@
class Rf a where
    toDist :: a -> Dist n a
    fromDist :: Dist n a -> a

instance Rf Int where
    toDist r = LInt r
    fromDist (LInt r) = r

instance (Rf a, Rf b) => Rf (a, b) where
    toDist (x, y) = Pair x' (toDist y)
      where
        x' :: Dist 0 a
        x' = toDist x
    fromDist (Pair e1 e2) = (fromDist e1, fromDist e2)

instance forall a b. (Rf a, Rf b) => Rf (a :&: b) where
    toDist :: forall n. (Rf a, Rf b) => (a :&: b) -> Dist n (a :&: b)
    toDist (a :&: b) = TPair a' b'
      where
        a' :: Dist n a
        a' = toDist a
        b' :: Dist n b
        b' = toDist b
    fromDist (TPair (e1 :: Dist nF a) (e2 :: Dist nS b)) =
        fromDist e1 :&: fromDist e2

instance (Rf a) => Rf (Vec 'L1 l a) where
    toDist VNil = DNil
    toDist (VCons x xs) = DCons x' (toDist xs)
      where
        x' :: Dist 0 a
        x' = toDist x

    fromDist DNil = VNil
    fromDist (DCons (e1 :: Dist nH a) (e2 :: Dist nT (Vec 'L1 l' a))) =
        VCons (fromDist e1) (fromDist e2)

instance forall l a. (Rf a) => Rf (Vec 'LInf l a) where
    toDist :: forall n. (Rf a) => Vec 'LInf l a -> Dist n (Vec 'LInf l a)
    toDist VNil = TNil
    toDist (VCons x (xs :: Vec 'LInf n1 a)) = TCons x' xs'
      where
        x' :: Dist n a
        x' = toDist x
        xs' :: Dist n (Vec 'LInf n1 a)
        xs' = toDist xs

    fromDist TNil = VNil
    fromDist (TCons (e1 :: Dist nH a) (e2 :: Dist nT (Vec 'LInf l' a))) =
        VCons (fromDist e1) (fromDist e2)

instance (Rf a) => Rf (Set a) where
    toDist = DSet
    fromDist (DSet s) = s

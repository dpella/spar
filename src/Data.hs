{-
  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at https://mozilla.org/MPL/2.0/.
-}

module Data where

import GHC.TypeLits (Nat, type (+))

-- | Allowed norms for vectors and pairs
data Norm = L1 | LInf

-- | Vectors: Fixed-length lists with an associated norm
data Vec (norm :: Norm) (n :: Nat) a where
    VNil :: Vec norm 0 a
    VCons :: a -> Vec norm n a -> Vec norm (n + 1) a

deriving instance (Show a) => Show (Vec norm n a)

-- | Pairs: A pair of elements different from haskell tuples
data a :&: b = a :&: b

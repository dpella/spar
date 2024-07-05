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

-- For addition
{-# OPTIONS_GHC -fplugin ThoralfPlugin.Plugin #-}

module Spar
  (
    Dist ()
  , Range (..)
  , Sen  ()
  , Vec  ()
  , PM
    -- No patterns (producers)
  , number
  , constant
  , addConstant
  , (.+)
  , cswp
  , up
  , up2
  , set
  , empty
  , union
  , difference
  , intersect
  , insertToSet
  , size
  , size'
  , setSplit
  , setMap
  , setFilter
  , setSum
  , clip
  , vecSplit
    -- Sensitive functions
  , sCurry
  , sUncurry
    -- Patterns (producer and consumer)
  , pattern (:*:)
  , pattern (:**:)
  , pattern Nil
  , pattern (:>)
  -- Use proven sensible functions
  , run
  -- Differential privacy
  , Epsilon
  , SetOrigin
  , laplace
  , addNoise
  , pattern (::>)
  , pattern NNil
  , dpReturn
  , dpBind
  , runPM
  )
where

import Statistics.Distribution ( genContVar )
import qualified Statistics.Distribution.Laplace as LapDistr
import System.Random.MWC ( createSystemRandom )
import Data.Proxy ( Proxy(Proxy) )
import GHC.TypeLits ( type (+), type (*), type (-), Nat, KnownNat, natVal, type (<=) )
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality ((:~:)(Refl), gcastWith )
import Data ( Vec(..), Norm(..), type (:&:) )
import Run ( Rf(..) )
import Deep ( up, Dist(..), up2, dpReturn, dpBind, PM (PM), dpLift )
import ManualProof ( plusEqZero3, plusEqZero4)
import Data.Constraint.Nat (Max)


--------------------------------------------------------------------------------
-- * Types

-- | Range data type to keep information at the type-level
data Range (min :: Nat) (max :: Nat) = Range

-- | Proof of sensitivity over uncurried functions
type Sen (k :: Nat) a b = forall n. Dist n a -> Dist (k*n) b

-- | Privacy budget
type Epsilon = Double

-- | Type of original dataset
type SetOrigin db = Set db

--------------------------------------------------------------------------------
-- * Useful operations

-- ** Basic primitives

-- | Create a relational number
number :: forall n . Int -> Dist n Int
number  = LInt

-- | Create a constant
constant :: Int -> Dist 0 Int
constant = number @0

-- | Add two relational numbers
(.+) :: Dist n1 Int -> Dist n2 Int -> Dist (n1+n2) Int
(LInt n) .+ (LInt m) = LInt (n+m)

-- | Compare the elements of a relational pair and swap them if necessary, i.e.,
-- the minimum is the first element and the maximum is the second.
--
-- Note: We do not allow to pattern match on CSwp. It doesn't make sense to go
-- back to the original pair
cswp :: Sen 1 (Int,Int) (Int,Int)
cswp (Pair n1@(LInt i1) n2@(LInt i2))
  | i1 <= i2  = n1 :*: n2
  | otherwise = n2 :*: n1

-- ** Set primitives

-- | Create a relational set
set :: forall n a. Set a -> Dist n (Set a)
set = DSet

-- | Create an empty set
empty :: Dist 0 (Set a)
empty = DSet (Set.empty)

-- | Insert an element into a relational set
insertToSet :: Ord a => a -> Dist n (Set a) -> Dist (n + 1) (Set a)
insertToSet v (DSet s) = DSet (Set.insert v s)

-- | Union of two relational sets
union :: Ord a => Dist n (Set a, Set a) -> Dist n (Set a)
union (DSet s1 :*: DSet s2) = DSet (Set.union s1 s2)

-- | Intersection of two relational sets
intersect :: Ord a => Dist n (Set a, Set a) -> Dist n (Set a)
intersect (DSet s1 :*: DSet s2) = DSet (Set.intersection s1 s2)

-- | Difference of two relational sets
difference :: Ord a => Dist n (Set a, Set a) -> Dist n (Set a)
difference (DSet s1 :*: DSet s2) = DSet (Set.difference s1 s2)

-- | Size of a relational set
size :: Dist n (Set a) -> Dist n Int
size (DSet s) = number (Set.size s)

-- | Singleton relational set containing the size of the input set
size' :: Dist n (Set a) -> Dist n (Set Int)
size' (DSet s) = DSet (Set.insert (Set.size s) Set.empty)

-- | Map a non-relational function over a relational set
--
-- NOTE: This function is defined in Fuzz
setMap :: Ord b => (a -> b) -> Dist n (Set a) -> Dist n (Set b)
setMap f (DSet s) = DSet (Set.map f s)

-- | Filter a relational set
--
-- NOTE: This function is defined in Fuzz
setFilter :: (a -> Bool) -> Dist n (Set a) -> Dist n (Set a)
setFilter f (DSet s) = DSet $ Set.filter f s

-- | Map a numeric function over a relational set, clip the result withing the
-- provided range, and sums these clipped values.
--
-- NOTE: Here, we connect distances of sets with distances of folding over it,
-- i.e., producing a result.
setSum :: forall n1 n2 a n . (n1 <= n2, KnownNat n1, KnownNat n2)
       => Range n1 n2 -> (a -> Int) -> Dist n (Set a) -> Dist (n*n2) Int
setSum r@Range f ds = LInt $ Set.foldr (+) 0 s
  where (DSet s) = setMap (clip r . f)  ds

-- | Clips a numeric value within a given range
clip :: forall n1 n2 a . (n1 <= n2, KnownNat n1, KnownNat n2, Num a, Ord a)
       => Range n1 n2 -> a -> a
clip _r i | i < minR   = minR
          | i > maxR   = maxR
          | otherwise = i
  where  minR = fromInteger $ natVal @n1 Proxy
         maxR = fromInteger $ natVal @n2 Proxy

-- | Split a relational set into two sets, one containing the elements that
-- satisfy the predicate and the other containing the elements that don't
setSplit
  :: forall n a.
     (a -> Bool)
  -> Dist n (Set a)
  -> Dist n (Set a, Set a)
setSplit f (DSet s) =
  let (s1, s2) = Set.partition f s
  in  (set @0 s1 :*: set @n s2) -- Ja!

-- | Add a constant to all elements of a relational set.
-- This is a derived function, with sensitivity 1.
addConstant :: (Ord b, Ord a) => b -> Dist n (Set a) -> Dist n (Set (b,a))
addConstant  b = setMap (\a -> (b,a))

-- ** Vector primitives

-- | Given a predicate, split a vector into two vectors, one containing the
-- elements that satisfy the predicate and the other containing the elements
-- that do not.
vecSplit
  :: forall l l1 l2 n. l ~ (l1 + l2)
  => (Int -> Bool) -> Dist n (Vec 'L1 l Int)
  -> Dist n (Vec 'L1 l1 Int, Vec 'L1 l2 Int)
vecSplit _f Nil = (fstVec :*: sndVec)
  where
    fstVec :: Dist n (Vec 'L1 l1 Int)
    fstVec = gcastWith (plusEqZero3 @l @l1 @l2 Refl Refl) Nil

    sndVec :: Dist 0 (Vec 'L1 l2 Int)
    sndVec = gcastWith (plusEqZero4 @l @l1 @l2 Refl Refl) Nil
vecSplit f (v@(LInt n) :> (vs :: Dist nT (Vec 'L1 m Int)))
  | f n = insertLeft @(l1 - 1) v (vecSplit f vs)
  | otherwise = insertRight @(l2 - 1) v (vecSplit f vs)
  where
    insertLeft :: forall l1' n1 n2.
                  Dist n1 Int -> Dist n2 (Vec 'L1 l1' Int, Vec 'L1 l2 Int)
               -> Dist (n1 + n2) (Vec 'L1 (l1' + 1) Int , Vec 'L1 l2 Int)
    insertLeft  v' (vs1 :*: vs2) = (v' :> vs1) :*: vs2

    insertRight :: forall l2' n1 n2.
                   Dist n1 Int -> Dist n2 (Vec 'L1 l1 Int, Vec 'L1 l2' Int)
                -> Dist (n1 + n2) (Vec 'L1 l1 Int , Vec 'L1 (l2' + 1) Int)
    insertRight v' (vs1 :*: vs2) = vs1 :*: (v' :> vs2)

--------------------------------------------------------------------------------
-- * Patterns

-- Relational pairs under the L1 norm
pattern (:*:) :: () =>
                 (r ~ (a, b), (nF + nS) ~ l)
                 =>
                 Dist nF a -> Dist nS b -> Dist l r
pattern d1 :*: d2 = Pair d1 d2

{-# COMPLETE (:*:) #-}

-- Relational pairs under the LInf norm
pattern (:**:) :: () =>
                 (r ~ (a :&: b), l ~ Max nS nF, nF <= l, nS <= l)
                 =>
                 Dist nF a -> Dist nS b -> Dist l r
pattern d1 :**: d2 = TPair d1 d2

{-# COMPLETE (:**:) #-}

-- Relational vectors under the L1 norm
pattern (:>) :: ()
                =>
                (r ~ Vec 'L1 (m + 1) a, (nH + nT) ~ l)
                =>
                Dist nH a -> Dist nT (Vec 'L1 m a) -> Dist l r
pattern (:>) a vs = DCons a vs

pattern Nil :: ()
               =>
               (l ~ n, r ~ Vec 'L1 0 a)
               =>
               Dist l r
pattern Nil = DNil

{-# COMPLETE Nil, (:>) #-}

-- Relational vectors under the LInf norm
pattern (::>) :: () => (l ~ Vec 'LInf (m + 1) a, n ~ Max nH nT) => Dist nH a
                    -> Dist nT (Vec 'LInf m a) -> Dist n l
pattern (::>) a vs = TCons a vs

pattern NNil :: ()
                =>
                (l ~ n, r ~ Vec 'LInf 0 a)
                =>
                Dist l r
pattern NNil = TNil

{-# COMPLETE NNil, (::>) #-}

--------------------------------------------------------------------------------
-- * Function sensitivity

-- | Curry a sensitive function
sCurry :: forall k a b c nF nS n . (n ~ (nF + nS)) =>
          Sen k (a,b) c -> Dist nF a -> Dist nS b -> Dist (k*n) c
sCurry f x y = f @(nF + nS) (x :*: y)

-- | Uncurry a sensitive function
sUncurry :: forall k a b c .
           (forall nF nS. Dist nF a -> Dist nS b -> Dist (k*(nF + nS)) c)
         -> Sen k (a,b) c
sUncurry f ((x :: Dist nF' a) :*: (y :: Dist nS' b)) = f @nF' @nS' x y
            -- We split n among x and y accordingly. Function f needs to be
            -- parametric in nF and nS

-- ** Execute a sensitive function

-- | Run a sensitive function
run :: forall k a b. (Rf a, Rf b) => Sen k a b -> a -> b
run f = fromDist . f . toDist

--------------------------------------------------------------------------------
-- * Laplace mechanism

-- | Laplace mechanism: taking as input a datasets at distance 1, computing the
-- sensitive measurement and returning the noisy result, where noise's scale is
-- determined by dataset's stability @s@, aggregations's sensitivity @k@, and
-- the privacy parameter @eps@.
laplace :: forall k c db db' eps d.
           (Rf db, Rf db', KnownNat k, KnownNat c, KnownNat eps, KnownNat d
           , ?d :: Proxy d)
        => Proxy eps
        -> Sen k (Set db') Int
        -> Sen c (SetOrigin db) (Set db')
        -> Dist 1 (SetOrigin db)
        -> PM eps Double
laplace proxyEps senA senT ddb = do
  let e'    = natVal proxyEps
  let d'    = natVal ?d
  let eps   = fromInteger e' / fromInteger d'
  let sen   = fromIntegral $ natVal (Proxy @k)
  let stb   = fromIntegral $ natVal (Proxy @c)
  let scale = (stb * sen) / eps
  let query = run (senA . senT)
  let db    = fromDist ddb
  let realV = query db
  let noise = dpLift $ sampleLaplace scale
  dpBind noise $ \n ->
    dpReturn $ fromIntegral realV  + n

-- | Sample from a Laplace distribution with mean 0 an scale @(stb*sen)/eps@
sampleLaplace :: Double -> IO Double
sampleLaplace lapScale = do
  let lap = LapDistr.laplace 0 lapScale
  gen <- createSystemRandom
  genContVar lap gen

-- | Generalization of the laplace mechanism a la Fuzz
addNoise :: forall n k a eps d .
            (?d :: Proxy d, KnownNat d, KnownNat eps, KnownNat n, KnownNat k
            , Rf a)
         => Proxy eps -> Sen k a Int -> Dist n a -> PM eps Double
addNoise proxyEps g da = do
  let e'      = natVal proxyEps
  let d'      = natVal ?d
  let eps     = fromInteger e' / fromInteger d'
  let sen     = fromIntegral $ natVal (Proxy @k)
  let stb     = fromIntegral $ natVal (Proxy @n)
  let scale   = (stb * sen) / eps
  let measure = run g
  let a = fromDist da
  let noise = dpLift $ sampleLaplace scale
  dpBind noise $ \n ->
    dpReturn $ fromIntegral (measure a) + n

-- | Run a computation with the privacy monad assigning a values for the epsilon
-- scaling factor
runPM :: KnownNat d1
      => Proxy d1 -> (forall d . (?d :: Proxy d, KnownNat d) => PM eps a)
      -> IO a
runPM d1 pm = let ?d = d1
              in case pm of
                   PM io -> io

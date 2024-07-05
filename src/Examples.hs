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

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}

-- Disable incomplete pattern warnings
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- Increase iterations to solve constraints
{-# OPTIONS_GHC -fconstraint-solver-iterations=0 #-}
-- For multiplication
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Examples where

import Spar

import Data (Norm (..), Vec (VCons, VNil), type (:&:))
import Data.Constraint (Dict (..), mapDict)
import qualified Data.List as List
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Type.Equality (gcastWith, (:~:) (Refl))
import GHC.TypeLits (KnownNat, type (+), type (*), type (<=), type (^))
import GHC.TypeNats (type (-))
import ManualProof (maxFst, maxSnd, proofGF, smart)
import Prelude hiding (return, (>>), (>>=))

--------------------------------------------------------------------------------
-- * Rebinding the monadic operations

-- | Operator (>>=) is redefined to use the privacy monad bind
(>>=) :: PM e a -> (a -> PM e' b) -> PM (e + e') b
(>>=) = dpBind

-- | The return function is redefined to use the privacy monad return
return :: a -> PM 0 a
return = dpReturn

--------------------------------------------------------------------------------
-- * Sorting

-- | Insert an element into a sorted vector using the L1 norm
insert ::
    forall nx nvec m.
    Dist nx Int ->
    Dist nvec (Vec 'L1 m Int) ->
    Dist (nx + nvec) (Vec 'L1 (m + 1) Int)
insert x Nil = x :> Nil
insert x ((y :: Dist nH a) :> (ys :: Dist nT (Vec 'L1 m' a))) =
    case cswp (x :*: y) of
        (a1 :: Dist nF t1) :*: (a2 :: Dist nS t2) ->
            gcastWith (smart @nF @nS @nT @nx @nvec Refl Refl)
                      (a1 :> insert a2 ys)

-- | Sort a vector using the L1 norm. It's distance remains the same
sort :: Dist l (Vec 'L1 m Int) -> Dist l (Vec 'L1 m Int)
sort Nil = Nil
sort (y :> ys) = insert y (sort ys)

-- | Proof that the sensitivity of the sort function is 1
fsort :: Sen 1 (Vec 'L1 m Int) (Vec 'L1 m Int)
fsort = sort

--------------------------------------------------------------------------------
-- * Mapping

-- | Map a k-sensitive function over a vector using the L1 norm
map' ::
    forall k n m a b.
    Sen k a b ->
    Dist n (Vec 'L1 m a) ->
    Dist (k * n) (Vec 'L1 m b)
map' _fun Nil = Nil
map' fun (x :> xs) = fun x :> map' fun xs

-- | Proof that map lifts a k-sensitive function to the level of vectors without
-- changing the sensitivity.
senMap' :: Sen k a b -> Sen k (Vec 'L1 m a) (Vec 'L1 m b)
senMap' = map'

--------------------------------------------------------------------------------
-- * Folding

-- ** Restricted folds

-- | FoldL a vector using the L1 norm and a 1-sensitive operator
foldL' ::
    forall nb nvec m a b.
    Sen 1 (a, b) b ->
    Dist nb b ->
    Dist nvec (Vec 'L1 m a) ->
    Dist (nb + nvec) b
foldL' _op b Nil = up b
foldL' op b (x :> xs) = foldL' op base xs
  where
    base = op (x :*: b)

-- I need to uncurry it first
ucfoldL' :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
ucfoldL' op (b :*: vec) = foldL' op b vec

ucfoldL2 :: forall a b m. Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
ucfoldL2 op = sUncurry @1 (foldL' op)

fucfoldL' :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
fucfoldL' f = ucfoldL' f

foldL :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
foldL _op (b :*: Nil) = up b
foldL op (b :*: (x :> xs)) = foldL op dist
  where
    dist = op (x :*: b) :*: xs

ffoldL :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
ffoldL = foldL

foldR :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
foldR _op (b :*: Nil) = up b
foldR op (b :*: (x :> xs)) = op (x :*: r)
  where
    r = foldR op (b :*: xs)

ffoldR :: Sen 1 (a, b) b -> Sen 1 (b, Vec 'L1 m a) b
ffoldR = foldR

-- ** Generic folds

-- | Generic foldr for a vector using the LInf norm and a k-sensitive operator.
foldrLInf ::
    forall nvec k m a b.
    (1 <= k, 0 <= m) =>
    Sen k (a :&: b) b ->
    Dist 0 b -> -- base case
    Dist nvec (Vec 'LInf m a) -> -- elements
    Dist ((k ^ m) * nvec) b
foldrLInf _f b NNil = up b
foldrLInf f b ((x :: Dist nH a) ::> (xs :: Dist nT (Vec 'LInf m' a))) =
    case proof of
        Dict -> f (x' :**: foldrLInf f b xs')
  where
    xs' :: Dist nvec (Vec 'LInf m' a)
    xs' = case pxs' of
        Dict -> up2 @nvec xs
    -- proof nT <= Max nH nT
    pxs' = mapDict (maxSnd @nH @nT @nvec) Dict

    x' :: Dist nvec a
    x' = case px' of
        Dict -> up2 @nvec x
    -- proof nH <= Max nH nT
    px' = mapDict (maxFst @nH @nT @nvec) Dict

    -- proof that nvec <= (k ^ m) * nvec
    proof = mapDict (proofGF @nvec @k @m') Dict

-- | Proof that a generic foldr for a vector using the LInf norm and a
-- k-sensitive operator returns a function of sensitivity k ^ m with @m@ the
-- length of the vector.
senFoldrLInf ::
    (1 <= k) =>
    Dist 0 b ->
    Sen k (a :&: b) b ->
    Sen (k ^ m) (Vec 'LInf m a) b
senFoldrLInf b f = foldrLInf f b

-- | Generic foldr for a vector using the L1 norm and a k-sensitive operator.
foldrL1 ::
    forall k nvec m a b.
    (1 <= k, 0 <= m) =>
    Sen k (a, b) b ->
    Dist 0 b ->
    Dist nvec (Vec 'L1 m a) ->
    Dist (m * (k ^ m) * nvec) b
foldrL1 _f b Nil = up b
foldrL1 f b (x :> (xs :: Dist nS (Vec 'L1 m1 a))) = f (x' :*: r)
  where
    r = foldrL1 f b (up2 @nvec xs)
    x' :: Dist (k ^ m1 * nvec) a
    x' = case proof of
        Dict -> up2 @(k ^ m1 * nvec) (up @nS x)
    proof = mapDict (proofGF @nvec @k @m1) Dict

-- | Proof that a generic foldr for a vector using the L1 norm and a k-sensitive
-- operator returns a function of sensitivity m * (k ^ m) with @m@ the length of
-- the vector.
senFoldrL1 ::
    (1 <= k, 0 <= m) =>
    Dist 0 b ->
    Sen k (a, b) b ->
    Sen (m * (k ^ m)) (Vec 'L1 m a) b
senFoldrL1 b f = foldrL1 f b

-- | Generic foldr1 for a vector using the LInf norm and a k-sensitive operator.
foldr1LInf ::
    forall k nvec m a.
    (1 <= k, 0 <= m) =>
    Sen k (a :&: a) a ->
    Dist nvec (Vec 'LInf m a) ->
    Dist ((k ^ m) * nvec) a
foldr1LInf _f ((x :: Dist nH a) ::> (NNil :: Dist nT (Vec 'LInf z a))) =
    case (p1, proof) of
        (Dict, Dict) -> up2 @(k ^ m * nvec) (up2 @nvec x)
  where
    p1 = mapDict (maxFst @nH @nT @nvec) Dict
    proof = mapDict (proofGF @nvec @k @(z + 1)) Dict
foldr1LInf f ((x :: Dist nH a) ::> (xs :: Dist nT (Vec 'LInf m' a))) =
    case proof of
        Dict -> f (x' :**: foldr1LInf f xs')
  where
    xs' :: Dist nvec (Vec 'LInf m' a)
    xs' = case p2 of
        Dict -> up2 @nvec xs
    p2 = mapDict (maxSnd @nH @nT @nvec) Dict

    x' :: Dist nvec a
    x' = case p1 of
        Dict -> up2 @nvec x
    -- proof nH <= Max nH nT
    p1 = mapDict (maxFst @nH @nT @nvec) Dict
    proof = mapDict (proofGF @nvec @k @m') Dict

-- | Proof that a generic foldr1 for a vector using the LInf norm and a
-- k-sensitive return a function of sensitivity k ^ m with @m@ the length of the
-- vector
senFoldr1LInf ::
    (1 <= k, 0 <= m) =>
    Sen k (a :&: a) a ->
    Sen (k ^ m) (Vec 'LInf m a) a
senFoldr1LInf = foldr1LInf

-- | Generic foldr1 for a vector using the L1 norm and a k-sensitive operator.
foldr1L1 ::
    forall k nvec m a.
    (1 <= k, 0 <= m) =>
    Sen k (a, a) a ->
    Dist nvec (Vec 'L1 m a) ->
    Dist (m * (k ^ m) * nvec) a
foldr1L1 _f (x :> Nil) = up2 @(k ^ m * nvec) (up2 @nvec x)
foldr1L1 f (x :> (xs :: Dist nS (Vec 'L1 m1 a))) = f (x' :*: r)
  where
    r = foldr1L1 f (up2 @nvec xs)
    x' :: Dist (k ^ m1 * nvec) a
    x' = case proof of
        Dict -> up2 @(k ^ m1 * nvec) (up @nS x)
    proof = mapDict (proofGF @nvec @k @m1) Dict

-- | Proof tha a generic foldr1 for a vector using the L1 norm and a k-sensitive
-- return a function of sensitivity m * (k ^ m) with @m@ the length of the
-- vector
senFoldr1L1 ::
    (1 <= k, 0 <= m) =>
    Sen k (a, a) a ->
    Sen (m * k ^ m) (Vec 'L1 m a) a
senFoldr1L1 = foldr1L1

--------------------------------------------------------------------------------

-- * Summing

-- | Sum all the elements in a vector using the L1 norm. Defined by pattern
-- matching on the vector.
sum' :: Dist n (Vec 'L1 m Int) -> Dist n Int
sum' Nil = number 0
sum' (x :> xs) = x .+ sum' xs

-- | Proof that the sensitivity of the sum function that pattern matches on
-- the vector is 1
senSum' :: Sen 1 (Vec 'L1 m Int) Int
senSum' = sum'

-- | Sum all the elements in a vector using the L1 norm. Defined by folding
-- over the vector with the addition function.
fsum :: Dist n (Vec 'L1 m Int) -> Dist n Int
fsum vec = ffoldL uPlus (constant 0 :*: vec)

-- | Proof that the sensitivity of the sum function that folds over the vector
-- is 1
senFsum :: Sen 1 (Vec 'L1 m Int) Int
senFsum = fsum

--------------------------------------------------------------------------------

-- * Appending

-- | Unccurried append function of two vectors using the L1 norm.
append :: Dist d (Vec 'L1 m Int, Vec 'L1 n Int) -> Dist d (Vec 'L1 (m + n) Int)
append (Nil :*: ys) = up ys
append ((x :> xs) :*: ys) = x :> append (xs :*: ys)

-- | Proof that the sensitivity of an unccurried append function is 1
senAppend :: Sen 1 (Vec 'L1 m Int, Vec 'L1 n Int) (Vec 'L1 (m + n) Int)
senAppend = append

-- | Curried append function of two vectors using the L1 norm.
append' ::
    Dist d1 (Vec 'L1 m Int) ->
    Dist d2 (Vec 'L1 n Int) ->
    Dist (d1 + d2) (Vec 'L1 (m + n) Int)
append' Nil ys = up ys
append' (x :> xs) ys = x :> append' xs ys

-- | Proof that the sensitivity of a curried append function is 1
senAppend' :: Sen 1 (Vec 'L1 m Int, Vec 'L1 n Int) (Vec 'L1 (m + n) Int)
senAppend' = sUncurry @1 append'

--------------------------------------------------------------------------------

-- * Concatenation

-- | Concatenates a vector of vectors using the L1 norm.
concat' :: Dist d (Vec 'L1 m (Vec 'L1 n Int)) -> Dist d (Vec 'L1 (m * n) Int)
concat' Nil = Nil
concat' (x :> xs) = append (x :*: concat' xs)

-- | Proof that the sensitivity of the concatenation function is 1
senConcat' :: Sen 1 (Vec 'L1 m (Vec 'L1 n Int)) (Vec 'L1 (m * n) Int)
senConcat' = concat'

--------------------------------------------------------------------------------

-- * Length

-- | Computes the length of a vector using the L1 norm, returning a pair
-- containing the length and the vector. While an unnecessary function since the
-- vectors are length-indexed, it serves as an example of how to handle
-- recursion. Note: Using let-in to pattern-match over the recursive call does
-- not work
len :: Dist n (Vec 'L1 l a) -> Dist n (Int, Vec 'L1 l a)
len Nil = constant 0 :*: Nil
len (x :> xs) =
  case len xs of
    (n :*: vs) -> (constant 1 .+ n) :*: (x :> vs)

-- | Obtains the length of a vector using the L1 norm.
len' :: Dist n (Vec 'L1 l a) -> Dist n Int
len' vs = case len vs of
    (n :*: _vs) -> up n

-- | Proof that the sensitivity of the length function returning the length and
-- original vector is 1
senLen :: Sen 1 (Vec 'L1 l a) (Int, Vec 'L1 l a)
senLen = len

-- | Proof that the sensitivity of the length function is 1
senLen' :: Sen 1 (Vec 'L1 l a) Int
senLen' = len'

--------------------------------------------------------------------------------

-- * Zipping

-- | Zips two vectors of the same size using the L1 norm.
zip' ::
    Dist d1 (Vec 'L1 n a) ->
    Dist d2 (Vec 'L1 n b) ->
    Dist (d1 + d2) (Vec 'L1 n (a, b))
zip' (x :> xs) (y :> ys) = (x :*: y) :> zip' xs ys
zip' Nil Nil = Nil

-- | Proof that the sensitivity of the zip function is 1
senZip' :: Sen 1 (Vec 'L1 n a, Vec 'L1 n b) (Vec 'L1 n (a, b))
senZip' (x :*: y) = zip' x y

-- | Unzips a vector of pairs using the L1 norm.
unzip' :: Dist d (Vec 'L1 n (a, b)) -> Dist d (Vec 'L1 n a, Vec 'L1 n b)
unzip' Nil = Nil :*: (Nil @0)
unzip' ((x :*: y) :> xys) = recCall $ unzip' xys
  where
    recCall (xs :*: ys) = (x :> xs) :*: (y :> ys)

-- | Proof that the sensitivity of the unzip function is 1
senUnzip' :: Sen 1 (Vec 'L1 n (a, b)) (Vec 'L1 n a, Vec 'L1 n b)
senUnzip' = unzip'

-- | Maps an operator over two given lists
zipWith' ::
    (d ~ (d1 + d2)) =>
    (forall d1' d2'. Dist d1' a -> Dist d2' b -> Dist (k * (d1' + d2')) c) ->
    Dist d1 (Vec 'L1 n a) ->
    Dist d2 (Vec 'L1 n b) ->
    Dist (k * d) (Vec 'L1 n c)
zipWith' op xs ys = map' (sUncurry op) (zip' xs ys)

-- | Proof that the zipWith lifts a k-sensitive operator to the level of vectors
-- preserving the same sensitivity
senZipWith ::
    Sen k (a, b) c ->
    Sen k (Vec 'L1 n a, Vec 'L1 n b) (Vec 'L1 n c)
senZipWith f = \(x :*: y) -> zipWith' (sCurry f) x y

--------------------------------------------------------------------------------

-- * Other examples from the literature

-- | Duplicates a given integer
dup :: Sen 2 Int Int
dup x = x .+ x

-- | Duplicates the value resulting from applying the given function to any
-- given number
twice :: Sen k Int Int -> Sen (2 * k) Int Int
twice f y = f y .+ f y

-- | Implements example given in Jazz's paper (Section 3.2)
jazz_ex :: Sen 4 Int Int
jazz_ex = twice dup

--------------------------------------------------------------------------------

-- * Non-private histograms

-- | A bucket is an integer
type Bucket = Int

-- | Given an initial bucket @c@ and a set of integers @dataset@, it creates a
-- histogram counting the number of elements in the dataset belonging to each
-- bucket. The buckets are apart by 10 units starting in @c@ and ending in 100.
hist' ::
    forall n.
    Bucket ->
    Dist n (Set Int) ->
    Dist n (Set (Bucket, Int))
hist' c dataset
    | c >= 101 = addConstant c (size' dataset)
    | otherwise =
        case setSplit @n @Int (\n -> c >= n) dataset of
            cBucket :*: rest ->
                let l = left cBucket
                    r = hist' (c + 10) rest
                 in (union (l :*: r))
  where
    left :: forall n'. Dist n' (Set Int) -> Dist n' (Set (Bucket, Int))
    left bucket = addConstant c (size' bucket)

-- | Create a histogram of a dataset with the initial bucket set to 0
hist :: forall n. Dist n (Set Int) -> Dist n (Set (Bucket, Int))
hist = hist' 0

-- | Proof that a histogram has sensitivity 1
senHist :: Sen 1 (Set Int) (Set (Bucket, Int))
senHist = hist

--------------------------------------------------------------------------------
-- * CDF satisfying differential privacy

-- | Implements an (m*eps)-DP CDF, with @m = length bks@
dpCDF' ::
    forall d l m eps.
    (?d :: Proxy d, KnownNat d, KnownNat eps) =>
    Vec l m Bucket ->
    Proxy eps ->
    Dist 1 (SetOrigin Int) ->
    PM (m * eps) [(Bucket, Double)]
dpCDF' VNil _eps _dataset = dpReturn []
dpCDF' (VCons b bks) eps dataset =
    let
        opDB :: forall n. Bucket -> Dist n (Set Int) -> Dist n (Set Int)
        opDB c s =
            case setSplit @n @Int (\z -> c >= z) s of
                cBucket :*: _rest -> up cBucket

        noisyCount :: Bucket -> PM eps Double
        noisyCount c = laplace @1 @1 eps size (opDB c) dataset
        --                         ^^^^^ while passed manually, the system will
        --                               reject any other value:r
        elemm = fmap (b,) (noisyCount b)
        rest = dpCDF' bks eps dataset
     in
        do
            x <- elemm
            r <- rest
            return (x : r)

-- | Implements an @eps@-DP CDF by distributing the given privacy budget among
-- the sub-queries
dpCDF ::
    (?d :: Proxy d, KnownNat d, KnownNat eps) =>
    Vec l m Bucket ->
    Proxy eps ->
    Dist 1 (SetOrigin Int) ->
    PM (m * eps) [(Bucket, Double)]
dpCDF bks totalEps = dpCDF' bks totalEps

-- | Executes a CDF example
runCDF :: IO [(Bucket, Double)]
runCDF =
    let db = Set.fromList [1 .. 100]
        totalEps = Proxy :: Proxy 1
        factor = Proxy :: Proxy 8
        bks =
          VCons 0 $ VCons 10 $ VCons 20 $ VCons 30 $
            VCons 40 $ VCons 50 $ VCons 60 $ VCons 70 VNil
     in runPM factor $ dpCDF bks totalEps (set db)

--------------------------------------------------------------------------------
-- * k-means

-- | Coordinates are integers
type PointX = Int
type PointY = Int

-- | A point is a pair of coordinates
type Point = (PointX, PointY)

-- | A centroid is a point
type Centroid = Point

-- | Adds all the x and y coordinates in a set of points in a differentially
-- private way. The sensitivity of the sum is determined by the range of the
-- values being added
addCoordinates ::
    forall n min max eps d.
    (?d :: Proxy d, KnownNat d, KnownNat eps, min <= max, KnownNat n,
    KnownNat min, KnownNat max) =>
    Range min max ->
    Proxy eps ->
    Dist n (Set Point) ->
    PM (2 * eps) Point
addCoordinates r proxyEps ps = do
    totX <- addNoise @n @max proxyEps sumXs ps -- :: PM eps Int
    totY <- addNoise @n @max proxyEps sumYs ps -- :: PM eps Int
    return (round totX, round totY)
  where
    sumXs :: Sen max (Set Point) Int
    sumXs = setSum r fst

    sumYs :: Sen max (Set Point) Int
    sumYs = setSum r snd

-- | Finds the center of a cluster of points by averaging their coordinates
findCenter ::
    forall n min max eps d.
    (KnownNat eps, ?d :: Proxy d, KnownNat d, min <= max, KnownNat n,
     KnownNat min, KnownNat max) =>
    Range min max ->
    Proxy eps ->
    Dist n (Set Point) ->
    PM (3 * eps) Centroid
findCenter r proxyEps ps = do
    (sumXs, sumYs) <- addCoordinates r proxyEps ps -- :: PM (2*eps) Point
    t <- addNoise @n @1 proxyEps size ps           -- :: PM eps Double
    let t' = round t
        centerX = sumXs `div` t'
        centerY = sumYs `div` t'
        centerX' = clip r centerX
        centerY' = clip r centerY
    return (centerX', centerY')

-- | Given a list of centroids and a set of points, assigns each point to the
-- closest centroid
assign :: [Centroid] -> Dist n (Set Point) -> Dist n (Set (Centroid, Point))
assign cs ps = setMap f ps
  where
    f p = (closest p, p)
    closest (x, y) =
        fst $
            head $
                List.sortBy
                    s
                    [ ((cx, cy), abs (x - cx) + abs (y - cy))
                    | (cx, cy) <- cs
                    ]
    s (_, d) (_, d')
        | d == d' = EQ
        | d < d' = LT
        | otherwise = GT

-- | Obtain all the points associated to an specific centroid
pickPointsForCentroid ::
    Centroid ->
    Dist n (Set (Centroid, Point)) ->
    Dist n (Set Point)
pickPointsForCentroid c = setMap snd . setFilter (\(c', _p) -> c' == c)

-- | Transforms a vector into a list
vecToList :: Vec l k a -> [a]
vecToList VNil = []
vecToList (VCons c cs) = c : vecToList cs

-- | Given a list of centroids and a set of points, partitions the points into
-- sets of points associated to each centroid
partition ::
    Vec l k Centroid ->
    Dist n (Set Point) ->
    Vec l k (Dist n (Set Point))
partition cs ps =
    let pointsWithCentroids = assign (vecToList cs) ps
     in partition' cs pointsWithCentroids
  where
    partition' ::
        Vec l k Centroid ->
        Dist n (Set (Centroid, Point)) ->
        Vec l k (Dist n (Set Point))
    partition' VNil _psCs = VNil
    partition' (VCons c' cs') psCS =
        VCons (pickPointsForCentroid c' psCS) (partition' cs' psCS)

-- | Given a list of centroids and, a set of points, and vector with indexed
-- length @iter@ representing the number of iterations, returns the centroids
-- that best represent the points
kmean ::
    forall n min max eps l iter k d.
    (?d :: Proxy d, KnownNat d, KnownNat eps, min <= max, KnownNat n,
    KnownNat min, KnownNat max, KnownNat (max - min)) =>
    Vec l iter () ->       -- number of iterations
    Range min max ->       -- range of x and y coordinates
    Proxy eps ->           -- Epsilon
    Vec l k Centroid ->    -- Initial centroids
    Dist n (Set Point) ->  -- Confidential points
    PM (iter * (3 * eps * k)) (Vec l k Centroid)
kmean VNil _r _eps cs _ps = dpReturn cs
kmean (VCons () us) r eps cs ps = do
    let parts = partition cs ps
    cs' <- vecSeq $ mapVec (findCenter @n @min @max @eps @d r eps) parts
    kmean us r eps cs' ps

-- | Maps a function over a vector
mapVec :: (a -> b) -> Vec l k a -> Vec l k b
mapVec _f VNil = VNil
mapVec f (VCons a as) = VCons (f a) (mapVec f as)

-- | Sequentially executes a vector of monadic actions
vecSeq :: Vec l k (PM eps a) -> PM (eps * k) (Vec l k a)
vecSeq VNil = return VNil
vecSeq (VCons pm pms) = do
    a <- pm
    as <- vecSeq pms
    return (VCons a as)

--------------------------------------------------------------------------------
-- * Helper functions

-- | Error message for impossible cases
err :: a
err = error "The impossible has happened!"

-- | Uncurried addition
uPlus :: Dist n (Int, Int) -> Dist n Int
uPlus (x :*: y) = x .+ y
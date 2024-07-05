{-
  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at https://mozilla.org/MPL/2.0/.
-}
{-# LANGUAGE CPP #-}

#ifdef MIN_VERSION_GLASGOW_HASKELL
#if MIN_VERSION_GLASGOW_HASKELL(8,6,0,0)
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE QuantifiedConstraints #-}
#endif
#endif

module ManualProof where

import Data.Type.Equality ((:~:) (Refl))
import qualified Data.Type.Equality as TyEq
import GHC.TypeLits ( type (+), type (*), type (^), type (<=) )
import Data.Constraint
import Data.Constraint.Nat (
    Max,
    eqLe,
    leTrans,
    leZero,
    plusAssociates,
    plusMonotone1,
    plusMonotone2,
    powMonotone2,
    powZero,
    timesMonotone1,
    zeroLe,
 )
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

-- * Helpers for Examples.insert

-- We know that
-- HA : (n1 + n2) ~ (a + c)
-- HB : (c + n3) ~ b
-- unifyAdd : x ~ y, then x + d ~ y + d (this is true and Haskell confirms it)
--
-- We want to prove
-- Goal: (n1 + (n2 + n3)) ~ (a+b)

-- We asked Haskell's type-checker to verify that if x ~ y, then it is the case
-- that (x + d) ~ (y + d). If type-checks, it is true!
unifyAdd :: forall x y d. (x ~ y) :- ((x + d) ~ (y + d))
unifyAdd = implied @(x ~ y) @((x + d) ~ (y + d))

-- We derive useful facts from (n1 + n2) ~ (a + c) by using the associativity of
-- + (see Data.Constraint.Nat.plusAssociates) and unifyAdd
auxiliary ::
    forall n1 n2 n3 a c.
    ((n1 + n2) ~ (a + c))
        :- ( ( ((n1 + n2) + n3) ~ ((a + c) + n3)
             , ((n1 + n2) + n3) ~ (n1 + (n2 + n3))
             )
           , ((a + c) + n3) ~ (a + (c + n3))
           )
auxiliary =
  strengthen2 (plusAssociates @a @c @n3)   -- *2) (a+c) + n3 ~ a + (c + n3)
  $
  strengthen2 (plusAssociates @n1 @n2 @n3) -- *3) (n1 + n2) + n3 ~ n1 + (n2 + n3)
  $
  unifyAdd @(n1+n2) @(a+c) @n3             -- *1) if (n1 + n2) ~ (a + c), then
                                           --     (n1 + n2) + n3 ~ (a + c) + n3

-- We use the derived facts together with the hypotheses to provide the type
-- checker with enough evidence to prove our goal.
smart ::
    forall n1 n2 n3 a b c.
    (n1 + n2) :~: (a + c) ->
    (c + n3) :~: b ->
    (n1 + (n2 + n3)) :~: (a + b)
smart Refl Refl =
    -- n1 + n2 ~ (a + c), (c + n3) ~ b
    case proof of
        Dict -> Refl
  where
    proof = mapDict (auxiliary @n1 @n2 @n3 @a @c) Dict

--------------------------------------------------------------------------------

-- * Helpers for Run module

-- | We want to prove that if n + m ~ 0 implies n ~ 0.
plusEqZeroEntailment1 :: forall n m. ((n + m) ~ 0) :- (n ~ 0)
plusEqZeroEntailment1 =
    trans
        -- n <= 0 :- n ~ 0
        (leZero @n)
        -- n + m ~ 0 :- n <= 0
        ( trans
            -- (n + m <= 0, n <= n + m) :- n <= 0
            (leTrans @n @(n + m) @0)
            -- n + m ~ 0 :- (n + m <= 0, n <= n + m)
            ( strengthen2
                -- Dict (n <= n + m)
                ( mapDict
                    -- 0 <= m :- n <= n + m
                    (plusMonotone2 @n @0 @m)
                    -- Dict (0 <= m)
                    (zeroLe @m)
                )
                -- n + m ~ 0 :- (n + m) <= 0
                (eqLe @(n + m) @0)
            )
        )

-- | We want to prove that n + m ~ 0 implies m ~ 0.
plusEqZeroEntailment2 :: forall n m. ((n + m) ~ 0) :- (m ~ 0)
plusEqZeroEntailment2 =
    trans
        -- m <= 0 :- m ~ 0
        (leZero @m)
        -- n + m ~ 0 :- m <= 0
        ( trans
            -- (n + m <= 0, m <= n + m) :- m <= 0
            (leTrans @m @(n + m) @0)
            -- n + m ~ 0 :- (n + m <= 0, m <= n + m)
            ( strengthen2
                -- Dict (m <= n + m)
                ( mapDict
                    -- 0 <= n :- m <= n + m
                    (plusMonotone1 @0 @n @m)
                    -- Dict (0 <= n)
                    (zeroLe @n)
                )
                -- n + m ~ 0 :- (n + m) <= 0
                (eqLe @(n + m) @0)
            )
        )

-- | Proof that if n + m is equivalent to 0, then n is equivalent to 0.
plusEqZero1 :: forall n m. (n + m) :~: 0 -> n :~: 0
plusEqZero1 Refl =
    case proof of
        Dict -> Refl
  where
    proof = mapDict (plusEqZeroEntailment1 @n @m) Dict

-- | Proof that if n + m is equivalent to 0, then m is equivalent to 0.
plusEqZero2 :: forall n m. (n + m) :~: 0 -> m :~: 0
plusEqZero2 Refl =
    case proof of
        Dict -> Refl
  where
    proof = mapDict (plusEqZeroEntailment2 @n @m) Dict

--------------------------------------------------------------------------------

-- * Helpers for API.splitVec

-- | Proof that if m + o ~ n and n ~ 0 then m ~ 0.
plusEqZero3 :: forall n m o. (m + o) :~: n -> n :~: 0 -> m :~: 0
plusEqZero3 x y = plusEqZero1 @m @o (TyEq.trans x y)

-- | Proof that if m + o ~ n and n ~ 0 then o ~ 0.
plusEqZero4 :: forall n m o. (m + o) :~: n -> n :~: 0 -> o :~: 0
plusEqZero4 x y = plusEqZero2 @m @o (TyEq.trans x y)

--------------------------------------------------------------------------------

-- * Auxiliary proof to get the generic fold with LInf

-- | We want to prove that 1 ~ k^0 implies 1 <= k^0.
unifyLessEq :: forall k. (1 ~ (k ^ 0)) :- (1 <= k ^ 0)
unifyLessEq = eqLe

-- | We want to prove that 0 <= m implies 0 <= m and 1 ~ (k^0).
introUnify :: forall k m. (0 <= m) :- (0 <= m, 1 ~ (k ^ 0))
introUnify = strengthen2 z refl
  where
    z = powZero @k

-- | We want to prove that 0 <= m and 1 ~ (k^0) implies 1 ~ (k^0).
positiveM :: forall k m. (0 <= m, 1 ~ (k ^ 0)) :- (1 ~ (k ^ 0))
positiveM = weaken2

-- | We want to prove that 0 <= m implies 1 <= k^0.
addPositiveHyp :: forall k m. (0 <= m) :- (1 <= k ^ 0)
addPositiveHyp = trans (trans unifyLessEq positiveM) introUnify

-- | We want to prove that 0 <= m implies 1 <= k^m.
-- Note: This is and error in the library, it should only hold for k > 0.
expMon :: forall k m. (0 <= m) :- (k ^ 0 <= k ^ m)
expMon = powMonotone2 @k @0 @m

-- | We want to prove that 0 <= m implies k^0 <= k^m and 1 <= k^0.
almostTrans :: forall k m. (0 <= m) :- (k ^ 0 <= k ^ m, 1 <= k ^ 0)
almostTrans = expMon @k @m &&& addPositiveHyp @k @m

-- | We want to prove that (k^0) <= (k^m) and 1 <= (k^0) implies 1 <= (k^m).
transitivity :: forall k m. ((k ^ 0) <= (k ^ m), 1 <= (k ^ 0)) :- (1 <= (k ^ m))
transitivity = leTrans @1 @(k ^ 0) @(k ^ m)

-- | We want to prove that 1 <= (k^m) implies 1*n <= (k^m)*n.
multIneq :: forall n k m. (1 <= k ^ m) :- (1 * n <= (k ^ m) * n)
multIneq = timesMonotone1 @1 @(k ^ m) @n

-- | We want to prove that 0<=m implies 1 <= k^m.
step :: forall k m. (0 <= m) :- (1 <= k ^ m)
step = trans (transitivity @k @m) (almostTrans @k @m)

-- | We want to prove that 0<=m implies n <= (k^m)*n.
proofGF :: forall n k m. (0 <= m) :- (n <= (k ^ m) * n)
proofGF = trans (multIneq @n @k @m) (step @k @m)

-- | We want to prove that l ~ Max n m implies n <= l.
-- Note: Assumed as axiom (missing in current library)
maxFst :: forall n m l . (l ~ Max n m) :- (n <= l)
maxFst = Sub unsafeAxiom

-- | We want to prove that l ~ Max n m implies m <= l.
-- Note: Assumed as axiom (missing in current library)
maxSnd :: forall n m l . (l ~ Max n m) :- (m <= l)
maxSnd = Sub unsafeAxiom

-- | Unsafe coercion to get the proof of a Dict c.
unsafeAxiom :: Dict c
unsafeAxiom = unsafeCoerce (Dict :: Dict ())

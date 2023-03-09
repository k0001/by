{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

#include <MachDeps.h>

module By.Interval {--}
  ( -- * Interval
    Interval
    -- ** Introduction
  , known
  , min
  , max
  , single
  , from
  , clamp
  , upcast
  , downcast
  , pred
  , succ
    -- ** Elimination
  , with
  , toInt
  , toWord
  , toCSize
  , toInteger
  , toNatural
    -- ** Invariants
  , absurdMinMax
  , absurdMax
    -- * Misc
  , MaxInt
  ) --}
where

import Control.Monad
import Data.Coerce
import Data.Constraint
import Data.Ord qualified
import Data.Proxy
import Data.Type.Ord
import Data.Void
import Foreign.C.Types (CSize (..))
import GHC.TypeNats
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (min, max, succ, pred, toInteger)
import Prelude qualified

--------------------------------------------------------------------------------

-- | Type-level version of @'maxBound' :: 'Int'@.
-- This value is machine-dependent.
#if WORD_SIZE_IN_BITS == 64
type MaxInt = 9223372036854775807
#elif WORD_SIZE_IN_BITS == 32
type MaxInt = 2147483647
#else
#error Unknown WORD_SIZE_IN_BITS
#endif

-- | An natural number known to be at least @l@, at most @r@.
--
-- * Construct safely with 'known', 'clamp', 'from', 'upcast' or 'downcast'.
--
-- * @l@ can be at most @r@ (see 'absurdMinMax').
--
-- * @r@ can be at most 'MaxInt' (see 'absurdMax').
newtype Interval (l :: Nat) (r :: Nat) = UnsafeInterval Int
  deriving newtype (Eq, Ord, Show)

absurdMinMax :: forall l r. (r < l) => Interval l r -> Void
absurdMinMax !_ = error "By.absurdMinMax"

-- | This upper bound for @r@ is there because this 'Interval' is used to index
-- byte containers in the "By" module, and allmost all Haskell containers use
-- 'Int' rather than the ideal 'Word' for conveying sizes and indexes. Having
-- this constraint makes ergonomics a bit better.
absurdMax :: forall l r. (MaxInt < r) => Interval l r -> Void
absurdMax !_ = error "By.absurdMax"

upcast
  :: forall ld rd lu ru
  .  (lu <= ld, lu <= ru, rd <= ru, ru <= MaxInt)
  => Interval ld rd
  -> Interval lu ru
upcast = coerce

downcast
  :: forall lu ru ld rd
  .  (KnownNat ld, KnownNat rd)
  => Interval lu ru
  -> Maybe (Interval ld rd)
downcast = from . toInt

with
  :: forall l r a
  .  (KnownNat l, KnownNat r)
  => Interval l r
  -> (forall n. (KnownNat n, l <= n, n <= r, r <= MaxInt) => Proxy n -> a)
  -> a
with i f
  | SomeNat (pn :: Proxy n) <- someNatVal (toNatural i)
  , Just Dict <- le @l @n
  , Just Dict <- le @n @r
  , Just Dict <- le @r @MaxInt
  = f pn
  | otherwise = error "with: impossible"

toInt :: forall l r. Interval l r -> Int
toInt = coerce

toWord :: forall l r. Interval l r -> Word
toWord = fromIntegral . toInt

toCSize :: forall l r. Interval l r -> CSize
toCSize = fromIntegral . toInt

toInteger :: forall l r. Interval l r -> Integer
toInteger = fromIntegral . toInt

toNatural :: forall l r. Interval l r -> Natural
toNatural = fromIntegral . toInt

known
  :: forall n l r
  .  (KnownNat n, l <= n, n <= r, r <= MaxInt)
  => Interval l r
known = UnsafeInterval (fromIntegral (natVal (Proxy @n)))

min
  :: forall l r
  .  (KnownNat l, l <= r, r <= MaxInt)
  => Interval l r
min = known @l

max
  :: forall l r
  .  (KnownNat r, l <= r, r <= MaxInt)
  => Interval l r
max = known @r

single
  :: forall n
  .  (KnownNat n, n <= MaxInt)
  => Interval n n
single = known @n

succ
  :: forall l r
  .  (KnownNat l, KnownNat r)
  => Interval l r
  -> Maybe (Interval l r)
succ i0 = do
  let i1 = toInt i0
  guard (i1 /= maxBound)
  from (i1 + 1)

pred
  :: forall l r
  .  (KnownNat l, KnownNat r)
  => Interval l r
  -> Maybe (Interval l r)
pred i0 = do
  let i1 = toInt i0
  guard (i1 /= 0)
  from (i1 - 1)

clamp
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r, l <= r, r <= MaxInt)
  => n
  -> Interval l r
clamp =
    UnsafeInterval . fromIntegral . Data.Ord.clamp (l, r) . fromIntegral
  where
    l = natVal (Proxy @l) :: Natural
    r = natVal (Proxy @r) :: Natural

from
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r)
  => n
  -> Maybe (Interval l r)
from = \i0 -> do
    let i1 = Prelude.toInteger i0
    guard (l <= i1 && i1 <= r && r <= z)
    pure (UnsafeInterval (fromIntegral i0))
  where
    l = Prelude.toInteger (natVal (Proxy @l))
    r = Prelude.toInteger (natVal (Proxy @r))
    z = Prelude.toInteger (natVal (Proxy @MaxInt))

le :: forall l r
   .  (KnownNat l, KnownNat r)
   => Maybe (Dict (l <= r))
le = case cmpNat (Proxy @l) (Proxy @r) of
  EQI -> Just $ unsafeCoerce (Dict @())
  LTI -> Just $ unsafeCoerce (Dict @())
  GTI -> Nothing

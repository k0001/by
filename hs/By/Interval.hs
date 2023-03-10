{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StrictData #-}
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
  , plus
  , minus
    -- ** Elimination
  , with
  , toInt
  , toWord
  , toCSize
  , toInteger
  , toNatural
    -- * Misc
  , MaxInt
  , MaxWord
  ) --}
where

import Control.Monad
import Data.Constraint
import Data.Constraint.Nat
import Data.Proxy
import Data.Type.Ord
import Foreign.C.Types (CSize (..))
import GHC.TypeLits qualified as Lits
import GHC.TypeNats
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (min, max, succ, pred, toInteger)
import Prelude qualified

--------------------------------------------------------------------------------

-- | Type-level version of @'maxBound' :: 'Int'@.
-- This value is machine-dependent.
#if WORD_SIZE_IN_BITS == 64
type MaxInt = 9223372036854775807
type MaxWord = 18446744073709551615
#elif WORD_SIZE_IN_BITS == 32
type MaxInt = 2147483647
type MaxWord = 4294967295
#else
#error Unknown WORD_SIZE_IN_BITS
#endif

-- | An natural number known to be at least @l@, at most @r@.
--
-- * Construct safely with 'known', 'clamp', 'from', 'upcast' or 'downcast'.
data Interval (l :: Nat) (r :: Nat) where
  Interval :: (l <= n, n <= r, KnownNat l, KnownNat r, KnownNat n)
           => Proxy n
           -> Natural
           -> Interval l r

instance Eq (Interval l r) where
  a == b = toNatural a == toNatural b

instance Ord (Interval l r) where
  compare a b = compare (toNatural a) (toNatural b)

instance Show (Interval l r) where
  showsPrec n = showsPrec n . toNatural

upcast
  :: forall ld rd lu ru
  .  (KnownNat lu, KnownNat ru, lu <= ld, lu <= ru, rd <= ru)
  => Interval ld rd
  -> Interval lu ru
upcast (Interval (p :: Proxy n) n)
  = withDict (leTrans @lu @ld @n)
  $ withDict (leTrans @n @rd @ru)
  $ Interval p n

downcast
  :: forall lu ru ld rd
  .  (KnownNat ld, KnownNat rd)
  => Interval lu ru
  -> Maybe (Interval ld rd)
downcast = from . toNatural

with
  :: forall l r a
  .  Interval l r
  -> (forall n
        .  (KnownNat l, KnownNat r, KnownNat n, l <= n, n <= r, l <= r)
        => Proxy n
        -> Natural
        -> a)
  -> a
with (Interval (p :: Proxy n) n) f = withDict (leTrans @l @n @r) (f p n)

toInt :: forall l r. (r <= MaxInt) => Interval l r -> Int
toInt = fromIntegral . toNatural

toWord :: forall l r. (r <= MaxWord) => Interval l r -> Word
toWord = fromIntegral . toNatural

toCSize :: forall l r. (r <= MaxWord) => Interval l r -> CSize
toCSize = fromIntegral . toNatural

toInteger :: forall l r. Interval l r -> Integer
toInteger = fromIntegral . toNatural

toNatural :: forall l r. Interval l r -> Natural
toNatural = \(Interval _ n) -> n

known
  :: forall n l r
  .  (KnownNat l, KnownNat r, KnownNat n, l <= n, n <= r)
  => Interval l r
known = Interval (Proxy @n) (natVal (Proxy @n))

min
  :: forall l r
  .  (KnownNat l, KnownNat r, l <= r)
  => Interval l r
min = known @l

max
  :: forall l r
  .  (KnownNat l, KnownNat r, l <= r)
  => Interval l r
max = known @r

single
  :: forall n
  .  (KnownNat n)
  => Interval n n
single = known @n

succ
  :: forall l r
  .  Interval l r
  -> Maybe (Interval l r)
succ i = with i $ \(_ :: Proxy n) n -> do
  guard (n < toNatural (max @l @r))
  from (n + 1)

pred
  :: forall l r
  .  Interval l r
  -> Maybe (Interval l r)
pred i = with i $ \(_ :: Proxy n) n -> do
  guard (n > toNatural (min @l @r))
  from (n - 1)

clamp
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r, l <= r)
  => n
  -> Interval l r
clamp n =
  let i = Prelude.toInteger n
  in case Lits.someNatVal i of
       Nothing -> min
       Just (SomeNat (px :: Proxy x)) ->
         case le @l @x of
           Nothing -> min
           Just Dict -> case le @x @r of
             Nothing -> max
             Just Dict -> Interval px (fromInteger i)

-- | @
-- a `plus` b  ==  a + b
-- @
plus :: forall la ra lb rb lc rc
     .  (KnownNat lc, KnownNat rc)
     => Interval la ra
     -> Interval lb rb
     -> Maybe (Interval lc rc)
plus a b = from (toInteger a + toInteger b)

-- | @
-- a `minus` b  ==  a - b
-- @
minus :: forall la ra lb rb lc rc
      .  (KnownNat lc, KnownNat rc)
      => Interval la ra
      -> Interval lb rb
      -> Maybe (Interval lc rc)
minus a b = from (toInteger a - toInteger b)

from
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r)
  => n
  -> Maybe (Interval l r)
from n = do
  let i = Prelude.toInteger n
  SomeNat (px :: Proxy x) <- Lits.someNatVal i
  Dict <- le @l @x
  Dict <- le @x @r
  pure $ withDict (leTrans @l @x @r) (Interval px (fromInteger i))

le :: forall l r
   .  (KnownNat l, KnownNat r)
   => Maybe (Dict (l <= r))
le = case cmpNat (Proxy @l) (Proxy @r) of
  EQI -> Just $ unsafeCoerce (Dict @())
  LTI -> Just $ unsafeCoerce (Dict @())
  GTI -> Nothing

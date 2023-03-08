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

module By {--}
  ( -- * Length
    GetLength (..)
  , LengthInterval
  , KnownLength(..)
  , lengthN

    -- * Allocation
  , Alloc (..)
  , alloc_
  , unsafeAlloc
  , unsafeAlloc_
  , allocN
  , allocN_
  , unsafeAllocN
  , unsafeAllocN_

    -- * Access
  , Access (..)
  , unsafeAccess

    -- * Sized
  , Sized
  , unSized
  , sized
  , unsafeSized
  , withSized
  , withSizedMinMax
  , withSizedMinMaxN

    -- * Byets
  , Byets

    -- * Base16
  , toBase16
  , toBase16N
  , fromBase16
  , showBase16
  , showsBase16
  , showStringBase16
  , base16Impl
  , Base16Impl(..)

    -- * Utils
  , pack
  , unpack
  , show
  , shows
  , showString
  , copy
  , copyN
  , replicate
  , replicateN
  , padLeftN
  , padRightN
  , append
  , appendN
  , take
  , takeN
  , drop
  , dropN
  , splitAt
  , splitAtN
  , concat

  -- * Endiannes
  , Endian(..)
  , Size

  -- * Interval
  , MaxInt
  , Interval
  , interval
  , intervalMin
  , intervalMax
  , intervalSingle
  , intervalFrom
  , intervalClamp
  , intervalUpcast
  , intervalDowncast
  , intervalInt
  , intervalCSize
  , intervalInteger
  , intervalNatural
  , intervalAbsurdLR
  , intervalAbsurdMax
  ) --}
where

import Control.Monad
import Data.Binary qualified as Bin
import Data.Binary.Get qualified as Bin
import Data.Binary.Put qualified as Bin
import Data.ByteString qualified as B
import Data.ByteString.Internal qualified as BI
import Data.Char (chr)
import Data.Coerce
import Data.Constraint
import Data.Constraint.Nat
import Data.Foldable qualified as F
import Data.Int
import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Ord
import Data.Proxy
import Data.String
import Data.Tagged
import Data.Type.Ord
import Data.Void
import Data.Word
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (ForeignPtr, withForeignPtr, newForeignPtr_)
import Foreign.Ptr (Ptr, nullPtr, plusPtr, castPtr)
import Foreign.Storable
import GHC.TypeLits qualified as GHC
import GHC.TypeNats
import Memzero qualified
import Prelude hiding (concat, length, replicate, shows, showString, take, drop,
  splitAt, show)
import Prelude qualified
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

-- | Type-level version of @'maxBound' :: 'Int'@. This value is machine-dependent.
type MaxInt = Div (2 ^ (Size Int * 8)) 2 - 1

-- | An natural number known to be at least @l@, at most @r@.
--
-- * Construct safely with 'interval', 'intervalClamp', 'intervalFrom',
-- 'intervalUpcast' or 'intervalDowncast'.
--
-- * @r@ can be at most 'MaxInt' (see 'intervalAbsurdMax').
--
-- * @l@ can be at most @r@ (see 'intervalAbsurdLR').
newtype Interval (l :: Nat) (r :: Nat) = UnsafeInterval Int
  deriving newtype (Eq, Ord, Show)

intervalAbsurdLR :: (r < l) => Interval l r -> Void
intervalAbsurdLR !_ = error "By.intervalAbsurdLR"

intervalAbsurdMax :: (MaxInt < r) => Interval l r -> Void
intervalAbsurdMax !_ = error "By.intervalAbsurdMax"

intervalUpcast
  :: forall ld rd lu ru
  .  (lu <= ld, lu <= ru, rd <= ru)
  => Interval ld rd
  -> Interval lu ru
intervalUpcast = coerce

intervalDowncast
  :: forall lu ru ld rd
  .  (KnownNat ld, KnownNat rd)
  => Interval lu ru
  -> Maybe (Interval ld rd)
intervalDowncast = intervalFrom . intervalInt

withInterval
  :: forall l r a
  .  (KnownNat l, KnownNat r)
  => Interval l r
  -> (forall n. (KnownNat n, l <= n, n <= r) => Proxy n -> a)
  -> a
withInterval i f
  | SomeNat (pn :: Proxy n) <- someNatVal (intervalNatural i)
  , Just Dict <- proveLE @l @n
  , Just Dict <- proveLE @n @r
  = f pn
  | otherwise = error "withInterval: impossible"

intervalInt :: Interval l r -> Int
intervalInt = coerce

intervalCSize :: Interval l r -> CSize
intervalCSize = fromIntegral . intervalInt

intervalInteger :: Interval l r -> Integer
intervalInteger = fromIntegral . intervalInt

intervalNatural :: Interval l r -> Natural
intervalNatural = fromIntegral . intervalInt

interval
  :: forall n l r
  .  (KnownNat n, l <= n, n <= r, r <= MaxInt)
  => Interval l r
interval = UnsafeInterval (fromIntegral (natVal (Proxy @n)))

intervalMin
  :: forall l r
  .  (KnownNat l, l <= r, r <= MaxInt)
  => Interval l r
intervalMin = interval @l

intervalMax
  :: forall l r
  .  (KnownNat r, l <= r, r <= MaxInt)
  => Interval l r
intervalMax = interval @r

intervalSingle
  :: forall n
  .  (KnownNat n, n <= MaxInt)
  => Interval n n
intervalSingle = interval @n

intervalClamp
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r, l <= r, r <= MaxInt)
  => n
  -> Interval l r
intervalClamp =
    UnsafeInterval . fromIntegral . clamp (l, r) . fromIntegral
  where
    l = natVal (Proxy @l) :: Natural
    r = natVal (Proxy @r) :: Natural

intervalFrom
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r)
  => n
  -> Maybe (Interval l r)
intervalFrom = \i0 -> do
    let i1 = toInteger i0
    -- We check (l <= r) and (r <= z) here so as to keep constraints simpler.
    guard (l <= i1 && i1 <= r && r <= z)
    pure (UnsafeInterval (fromIntegral i0))
  where
    l = toInteger (natVal (Proxy @l))
    r = toInteger (natVal (Proxy @r))
    z = toInteger (natVal (Proxy @MaxInt))

--------------------------------------------------------------------------------

type LengthInterval (t :: Type) = Interval (MinLength t) (MaxLength t)

-- | Runtime byte length discovery.
class
  ( KnownNat (MinLength t)
  , KnownNat (MaxLength t)
  , MinLength t <= MaxLength t
  , MaxLength t <= MaxInt
  ) => GetLength t where
  type MinLength (t :: Type) :: Natural
  type MaxLength (t :: Type) :: Natural
  length :: t -> LengthInterval t
  default length :: KnownLength t => t -> LengthInterval t
  length (_ :: t) = lengthN @t

-- | Statically known byte length.
class
  ( GetLength t
  , Length t ~ MinLength t
  , Length t ~ MaxLength t
  ) => KnownLength (t :: Type) where
  -- | Known fixed number of bytes of user data that fit in @t@.
  type Length t :: Natural
  type Length t = MinLength t

-- | Unique instance.
instance
  ( GetLength t
  , Length t ~ MinLength t
  , Length t ~ MaxLength t
  ) => KnownLength (t :: Type) where

-- | Get statically known byte length.
lengthN :: forall t. KnownLength t => LengthInterval t
lengthN = interval @(Length t)

-- | Raw byte access for read-only purposes.
--
-- __WARNING__ The “read-only” part is not enforced anywhere. Be careful.
class GetLength t => Access t where
  access :: t -> (Ptr Word8 -> IO a) -> IO a

-- | Like 'access', but “pure”. This is safe as long as the
-- passed in function only interacts with the 'length' bytes
-- starting at the given 'Ptr' in a read-only manner.
unsafeAccess
  :: Access t
  => t
  -> (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> a
unsafeAccess t g = unsafePerformIO (access t g)
{-# NOINLINE unsafeAccess #-}

-- | Arbitrary byte length allocation and initialization.
class GetLength t => Alloc t where
  alloc :: LengthInterval t
        -> (Ptr Word8 -> IO a)
        -- ^ Initialization procedure for 'length'
        -- bytes starting at the given 'Ptr'.
        -> IO (t, a)

-- | Like 'allocN', but the output from the initialization
-- procedure is discarded.
alloc_
  :: forall t a
  .  (Alloc t)
  => LengthInterval t
  -> (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> IO t
alloc_ n = fmap fst . alloc n

-- | Like 'allocN', but the output from the initialization
-- procedure is discarded.
allocN_
  :: forall t a
  .  (Alloc t, KnownLength t)
  => (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> IO t
allocN_ = fmap fst . allocN

-- | Fixed byte length allocation and initialization.
allocN
  :: forall t a
  .  (Alloc t, KnownLength t)
  => (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> IO (t, a)
allocN = alloc (lengthN @t)

-- | Like 'alloc', but “pure”. This is safe as long as the
-- initialization procedure only interacts with the 'length'
-- bytes starting at the given 'Ptr'.
unsafeAlloc
  :: forall t a
  .  Alloc t
  => LengthInterval t -- ^ 'length'.
  -> (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> (t, a)
unsafeAlloc len g = unsafePerformIO (alloc len g)
{-# NOINLINE unsafeAlloc #-}

-- | Like 'unsafeAlloc', but the output from the initialization
-- procedure is discarded.
unsafeAlloc_
  :: forall t a
  .  Alloc t
  => LengthInterval t -- ^ 'length'.
  -> (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> t
unsafeAlloc_ len g = fst (unsafeAlloc len g)

-- | Like 'allocN', but “pure”. This is safe as long as the
-- initialization procedure only interacts with @'Length' t@
-- bytes starting at the given 'Ptr'.
unsafeAllocN
  :: forall t a
  .  (Alloc t, KnownLength t)
  => (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for @'Length' t@
  -- bytes starting at the given 'Ptr'.
  -> (t, a)
unsafeAllocN = unsafeAlloc (lengthN @t)

-- | Like 'unsafeAllocN', but the output from the initialization
-- procedure is discarded.
unsafeAllocN_
  :: forall t a
  .  (Alloc t, KnownLength t)
  => (Ptr Word8 -> IO a)
  -- ^ Initialization procedure for @'Length' t@
  -- bytes starting at the given 'Ptr'.
  -> t
unsafeAllocN_ g = fst (unsafeAllocN g)

-- | @'replicate' n x@ repeats @n@ times the byte @x@.
replicate :: Alloc a => LengthInterval a -> Word8 -> a
replicate len x = unsafeAlloc_ len $ \p ->
                  c_memset p x (intervalCSize len)

-- | @'replicate' x@ repeats @'Length' a@ times the byte @x@.
replicateN :: forall a. (Alloc a, KnownLength a) => Word8 -> a
replicateN = replicate (lengthN @a)

-- | @'copyN' a@ copies all of @a@ into a newly allocated @b@, if it would fit.
copy :: forall a b. (Access a, Alloc b) => a -> Maybe b
copy a = do
   bL <- intervalDowncast (length a)
   pure $ unsafeAlloc_ bL $ \bP ->
          access a $ \aP ->
          c_memcpy bP aP (intervalCSize bL)

-- | @'copyN' a@ copies all of @a@ into a newly allocated @b@.
copyN
  :: forall a b
  .  ( Access a
     , Alloc b
     , MinLength b <= MinLength a
     , MaxLength a <= MaxLength b )
  => a
  -> b
copyN a =
  let aL = length a
  in  unsafeAlloc_ (intervalUpcast aL) $ \bP ->
      access a $ \aP ->
      c_memcpy bP aP (intervalCSize aL)

-- | @'append' a b@ allocates a new @c@ that contains the concatenation of
-- @a@ and @b@, in that order, if it would fit in @c@.
append
  :: forall a b c
  .  ( Access a
     , Access b
     , Alloc c )
  => a
  -> b
  -> Maybe c
append a b = do
  let aL = length a
      bL = length b
  cL <- intervalFrom (intervalInteger aL + intervalInteger bL)
  pure $ unsafeAlloc_ cL $ \cP ->
         access a $ \aP ->
         access b $ \bP -> do
           void $ c_memcpy cP aP (intervalCSize aL)
           void $ c_memcpy (plusPtr cP (intervalInt aL)) bP (intervalCSize bL)

-- | @'append' a b@ allocates a new @c@ that contains the concatenation of
-- @a@ and @b@, in that order.
appendN
  :: forall a b c
  .  ( Access a
     , Access b
     , Alloc c
     , MinLength c <= MinLength a + MinLength b
     , MaxLength a + MaxLength b <= MaxLength c )
  => a
  -> b
  -> c
appendN a b =
    unsafeAlloc_ cL $ \cP ->
    access a $ \aP ->
    access b $ \bP -> do
      void $ c_memcpy cP aP (intervalCSize aL)
      void $ c_memcpy (plusPtr cP (intervalInt aL)) bP (intervalCSize bL)
  where
    aL = length a
    bL = length b
    cL | SomeNat (_ :: Proxy cL) <-
           someNatVal (intervalNatural aL + intervalNatural bL)
       , Just Dict <- proveLE @cL @(MaxLength c)
       , Just Dict <- proveLE @(MinLength c) @cL
       = interval @cL
       | otherwise = error "By.append: impossible"

-- | @'splitAt' n a@ copies the @n@ leading bytes of @a@ into a newly
-- allocated @b@, and the trailing @'length' a - n@ bytes of @a@
-- into @b@, if they would fit.
splitAt
  :: forall a b c
  .  ( Access a
     , Alloc b
     , Alloc c )
  => LengthInterval a
  -> a
  -> Maybe (b, c)
splitAt bLa a = do
  let aL :: LengthInterval a = length a
  bL :: LengthInterval b <- intervalDowncast bLa
  cL :: LengthInterval c <- intervalFrom $ intervalInteger aL
                                         - intervalInteger bL
  pure $ unsafeAlloc bL $ \bP ->
         alloc_ cL $ \cP ->
         access a $ \aP -> do
           void $ c_memcpy bP aP (intervalCSize bL)
           c_memcpy cP (plusPtr aP (intervalInt bL)) (intervalCSize cL)

-- | @'splitAtN' a@ splits @a@ into two parts of known lengths.
--
-- The resulting parts are copies independent from @a@.
splitAtN
  :: forall a b c
  .  ( Access a
     , Alloc b
     , Alloc c
     , KnownLength b
     , KnownLength c
     , Length a ~ (Length b + Length c) )
  => a
  -> (b, c)
splitAtN =
  let bL = lengthN @b
      cL = lengthN @c
  in \a -> unsafeAllocN $ \bP ->
           allocN_ $ \cP ->
           access a $ \aP -> do
             void $ c_memcpy bP aP (intervalCSize bL)
             c_memcpy cP (plusPtr aP (intervalInt bL)) (intervalCSize cL)

-- | @'take' n a@ copies the @n@ leading bytes of @a@ into a
-- newly allocated @b@, if it would fit.
take
  :: forall a b.
     ( Access a
     , Alloc b )
  => LengthInterval a
  -> a
  -> Maybe b
take bLa a = do
  let aL :: LengthInterval a = length a
  guard (bLa <= aL)
  bL :: LengthInterval b <- intervalDowncast bLa
  pure $ unsafeAlloc_ bL $ \bP ->
         access a $ \aP ->
         c_memcpy bP aP (intervalCSize bL)

-- | @'dropN' a@ copies the leading bytes of @a@ into a
-- newly allocated @b@ of known length.
takeN
  :: forall a b.
     ( Access a
     , Alloc b
     , KnownLength b
     , Length b <= Length a )
  => a
  -> b
takeN =
  let bL = lengthN @b
  in  \a -> unsafeAllocN_ $ \bP ->
            access a $ \aP ->
            c_memcpy bP aP (intervalCSize bL)

-- | @'drop' n a@ copies the @n@ trailing bytes of @a@ into a newly
-- allocated @b@, if it would fit.
drop
  :: forall a b.
     ( Access a
     , Alloc b )
  => LengthInterval a
  -> a
  -> Maybe b
drop bLa a = do
  let aL :: LengthInterval a = length a
  guard (bLa <= aL)
  bL :: LengthInterval b <- intervalDowncast bLa
  let dL' :: Int = intervalInt aL - intervalInt bL
  pure $ unsafeAlloc_ bL $ \bP ->
         access a $ \aP ->
         c_memcpy bP (plusPtr aP dL') (intervalCSize bL)

-- | @'dropN' a@ copies the trailing bytes of @a@ into a
-- newly allocated @b@ of known length.
dropN
  :: forall a b.
     ( Access a
     , Alloc b
     , KnownLength a
     , KnownLength b
     , Length b <= Length a )
  => a
  -> b
dropN = \a ->
    unsafeAllocN_ $ \bP ->
    access a $ \aP ->
    c_memcpy bP (plusPtr aP pL') (intervalCSize bL)
  where
    aL = lengthN @a
    bL = lengthN @b
    pL' = intervalInt aL - intervalInt bL

-- | Allocate a new @a@ made up of the bytes in @f@.
-- 'Nothing' if the result wouldn't fit in @a@.
pack :: forall a f. (Alloc a, Foldable f) => f Word8 -> Maybe a
pack ws = do
  aL <- intervalFrom (F.length ws)
  pure $ unsafeAlloc_ aL $ \aP ->
         F.foldlM (\off w -> do c_memset (plusPtr aP off) w 1
                                pure $! off + 1)
                  0
                  ws

-- | List of bytes in @a@.
unpack :: Access a => a -> [Word8]
{-# NOINLINE unpack #-}
unpack a = unsafeDupablePerformIO $ access a (f (intervalInt (length a)))
  where
    f :: Int -> Ptr Word8 -> IO [Word8]
    f 0 !_ = pure []
    f n  p = do !x <- peek p
                !xs <- f (n - 1) (plusPtr p 1)
                pure (x : xs)

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.show'.
show :: Access a => a -> String
show = flip shows ""

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.shows'.
shows :: Access a => a -> ShowS
shows = Prelude.shows . fmap (chr . fromIntegral) . unpack

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.showString'.
showString :: Access a => a -> ShowS
showString = Prelude.showString . fmap (chr . fromIntegral) . unpack

-- | Encodes @a@ using Base-16 encoding and then renders it using 'show'.
showBase16
  :: forall a
  .  (Access a)
  => Bool -- Uppercase if 'True'.
  -> a
  -> String
showBase16 u a = showsBase16 u a ""

-- | Encodes @a@ using Base-16 encoding and then renders it using 'shows'.
showsBase16
  :: forall a
  .  (Access a)
  => Bool -- Uppercase if 'True'.
  -> a
  -> ShowS
showsBase16 u a = showChar '"' . showStringBase16 u a . showChar '"'

-- | Encodes @a@ using Base-16 encoding and then renders it
-- using 'showString'.
showStringBase16
  :: forall a
  .  (Access a)
  => Bool -- Uppercase if 'True'.
  -> a
  -> ShowS
showStringBase16 u a
  | Just aB16 <- toBase16 u a
      = showString (aB16 :: B.ByteString)
  | Just (b, c) <- splitAt bLa a
  , Just bB16 <- toBase16 u (b :: B.ByteString)
      = showString (bB16 :: B.ByteString)
      . showStringBase16 u (c :: B.ByteString)
  | otherwise = error "showsStringBase16: impossible"
  where
    bLa :: LengthInterval a
    bLa = intervalClamp (4096 :: Int)

-- | Concatenates all the @a@s. 'Nothing' if the result doesn't fit in @b@.
concat :: forall a b f. (Access a, Alloc b, Foldable f) => f a -> Maybe b
concat as = do
  -- We add lengths as 'Integer' to avoid overflowing 'Int' while adding.
  bL <- intervalFrom $ F.foldl' (\ !z a -> z + intervalInteger (length a)) 0 as
  pure $ unsafeAlloc_ bL $ \outP ->
         F.foldlM (\off a -> access a $ \aP -> do
                      let aL = length a
                      void $ c_memcpy (plusPtr outP off) aP (intervalCSize aL)
                      pure $! off + intervalInt aL)
         0
         as

--------------------------------------------------------------------------------

-- | Interpreted as 'nullPtr'.
instance Access () where
  access _ g = g nullPtr

instance GetLength () where
  type MinLength () = 0
  type MaxLength () = 0
  length () = interval @0

--------------------------------------------------------------------------------

newtype Sized (len :: Natural) t = Sized t
  deriving newtype (Show)

deriving newtype instance {-# OVERLAPPABLE #-} Eq t => Eq (Sized len t)
deriving newtype instance {-# OVERLAPPABLE #-} Ord t => Ord (Sized len t)

deriving newtype instance (GetLength (Sized len t), Access t)
  => Access (Sized len t)

instance (KnownNat len, MinLength t <= len, len <= MaxLength t, len <= MaxInt)
  => GetLength (Sized len t) where
  type MinLength (Sized len t) = len
  type MaxLength (Sized len t) = len

instance
  ( Alloc t
  , MinLength t <= len
  , len <= MaxLength t
  , KnownLength (Sized len t)
  ) => Alloc (Sized len t) where
  alloc l g = do
    (t, a) <- alloc (intervalUpcast l) g
    pure (Sized t, a)

instance KnownLength (Sized len B.ByteString)
  => Bin.Binary (Sized len B.ByteString) where
  put (Sized t) = Bin.putByteString t
  get = Sized <$> Bin.getByteString
                        (intervalInt (lengthN @(Sized len B.ByteString)))

unSized :: Sized len t -> t
unSized = coerce
{-# INLINE unSized #-}

-- | Wrap the @t@ in a 'Sized' if it has the correct length.
sized
  :: forall len t
  .  (KnownNat len, GetLength t)
  => t
  -> Maybe (Sized len t)
sized = \t -> do
  Dict <- proveLE @(MinLength t) @len
  Dict <- proveLE @len @(MaxLength t)
  Dict <- pure $ evidence $ leTrans @len @(MaxLength t) @MaxInt
  tL <- intervalFrom (intervalInt (length t))
  guard (tL == lengthN @(Sized len t))
  pure (Sized t)

-- | Wrap the @t@ in a 'Sized' if it has the correct length,
-- otherwise fail with 'error'.
unsafeSized
  :: forall len t
  .  (KnownNat len, GetLength t)
  => t
  -> Sized len t
unsafeSized = fromMaybe (error "By.unsafeSized") . sized

withSized
  :: forall t a
  .  GetLength t
  => t
  -> (forall len
        .  ( KnownLength (Sized len t)
           , MinLength t <= len
           , len <= MaxLength t )
        => Sized len t
        -> a)
  -> a
withSized = withSizedMinMaxN @(MinLength t) @(MaxLength t)

-- | Wrap the @t@ in a 'Sized' of some unknown length within @min@ and @max@.
withSizedMinMax
  :: forall min max t a
  .  ( GetLength t
     , KnownNat min
     , KnownNat max )
  => t
  -> ( forall len
       .  ( KnownLength (Sized len t)
          , min <= len
          , len <= max )
       => Sized len t
       -> a )
  -> Maybe a
withSizedMinMax t g = do
  SomeNat (_ :: Proxy len) <- pure $ someNatVal $ intervalNatural (length t)
  Dict <- proveLE @min @len
  Dict <- proveLE @len @max
  Dict <- proveLE @(MinLength t) @len
  Dict <- proveLE @len @(MaxLength t)
  Dict <- pure $ evidence $ leTrans @len @(MaxLength t) @MaxInt
  pure $ g (Sized t :: Sized len t)

-- | Wrap the @t@ in a 'Sized' of length known to be within @min@ and @max@.
withSizedMinMaxN
  :: forall min max t a
  .  ( GetLength t
     , min <= MinLength t
     , MaxLength t <= max
     , KnownNat min
     , KnownNat max )
  => t
  -> ( forall len
       .  ( KnownLength (Sized len t)
          , min <= len
          , len <= max )
       => Sized len t
       -> a )
  -> a
withSizedMinMaxN t = withInterval (length t) $ \(_ :: Proxy len) ->
  case evidence $ leTrans @min @(MinLength t) @len of
    Dict -> case evidence $ leTrans @len @(MaxLength t) @max of
      Dict -> case evidence $ leTrans @len @(MaxLength t) @MaxInt of
        Dict -> \f -> f (Sized t :: Sized len t)

proveLE
  :: forall l r
  .  (KnownNat l, KnownNat r)
  => Maybe (Dict (l <= r))
proveLE = case cmpNat (Proxy @l) (Proxy @r) of
  EQI -> Just $ unsafeCoerce (Dict @())
  LTI -> Just $ unsafeCoerce (Dict @())
  GTI -> Nothing

--------------------------------------------------------------------------------

type family Size (a :: Type) :: Natural

type instance Size Word8  = 1
type instance Size Word16 = 2
type instance Size Word32 = 4
type instance Size Word64 = 8
type instance Size Int8   = 1
type instance Size Int16  = 2
type instance Size Int32  = 4
type instance Size Int64  = 8
type instance Size CSize = Size Word

#if WORD_SIZE_IN_BITS == 64
-- | This value is machine-dependent.
type instance Size Int  = Size Int64
-- | This value is machine-dependent.
type instance Size Word = Size Word64
#elif WORD_SIZE_IN_BITS == 32
-- | This value is machine-dependent.
type instance Size Int  = Size Int32
-- | This value is machine-dependent.
type instance Size Word = Size Word32
#else
# error "Unexpected WORD_SIZE_IN_BYTES"
#endif

--------------------------------------------------------------------------------

-- | Conversion between host byte encoding and Little-Endian or
-- Big-Endian byte encoding.
class (KnownNat (Size a), Size a <= MaxInt) => Endian a where
  {-# MINIMAL hToLE, hToBE, leToH, beToH #-}
  -- | From host encoding to Little-Endian encoding.
  hToLE :: a -> Tagged "LE" a
  -- | From host encoding to Big-Endian encoding.
  hToBE :: a -> Tagged "BE" a
  -- | From Little-Endian encoding to host encoding.
  leToH :: Tagged "LE" a -> a
  -- | From Big-Endian encoding to host encoding.
  beToH :: Tagged "BE" a -> a

  -- | Writes @a@ in @h@ using the host encoding.
  encodeH
    :: forall h. (Alloc h, MinLength h <= Size a, Size a <= MaxLength h)
    => a -> h
  -- | Default implementation in case there is a @'Storable' a@ instance.
  default encodeH
    :: forall h
    .  (Alloc h, MinLength h <= Size a, Size a <= MaxLength h, Storable a)
    => a -> h
  encodeH = \a -> unsafeAlloc_ (interval @(Size a)) $ \p ->
                  poke (castPtr p) a

  -- | Writes @a@ in @le@ using Litle-Endian encoding.
  encodeLE
    :: forall le. (Alloc le, MinLength le <= Size a, Size a <= MaxLength le)
    => a -> le
  encodeLE = encodeH . unTagged . hToLE

  -- | Writes @a@ in @be@ using Big-Endian encoding.
  encodeBE
    :: forall be. (Alloc be, MinLength be <= Size a, Size a <= MaxLength be)
    => a -> be
  encodeBE = encodeH . unTagged . hToBE

  -- | Reads @a@ from @h@ using the host encoding.
  decodeH :: forall h. (Access h, Size a ~ Length h) => h -> a
  -- | Default implementation in case there is a @'Storable' a@ instance.
  default decodeH
    :: forall h. (Access h, Size a ~ Length h, Storable a) => h -> a
  decodeH h = unsafeDupablePerformIO $ access h (peek . castPtr)
  {-# NOINLINE decodeH #-}

  -- | Reads @a@ from @le@ using Little-Endian encoding.
  decodeLE :: forall le. (Access le, Size a ~ Length le) => le -> a
  decodeLE = leToH . Tagged . decodeH

  -- | Reads @a@ from @be@ using Big-Endian encoding.
  decodeBE :: forall be. (Access be, Size a ~ Length be) => be -> a
  decodeBE = beToH . Tagged . decodeH

instance Endian Word8 where
  hToLE = coerce
  hToBE = coerce
  leToH = coerce
  beToH = coerce

instance Endian Word16 where
  hToLE = coerce htole16
  hToBE = coerce htobe16
  leToH = coerce le16toh
  beToH = coerce be16toh

instance Endian Word32 where
  hToLE = coerce htole32
  hToBE = coerce htobe32
  leToH = coerce le32toh
  beToH = coerce be32toh

instance Endian Word64 where
  hToLE = coerce htole64
  hToBE = coerce htobe64
  leToH = coerce le64toh
  beToH = coerce be64toh

-- | This instance is machine-dependent.
instance Endian Int where
  hToLE = fmap (fromIntegral @Word) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word) . hToBE . fromIntegral
  leToH = fromIntegral @Word . beToH . fromIntegral . unTagged
  beToH = fromIntegral @Word . beToH . fromIntegral . unTagged

instance Endian Int8 where
  hToLE = coerce
  hToBE = coerce
  leToH = coerce
  beToH = coerce

instance Endian Int16 where
  hToLE = Tagged . fromIntegral . htole16 . fromIntegral
  hToBE = Tagged . fromIntegral . htobe16 . fromIntegral
  leToH = fromIntegral . le16toh . fromIntegral . unTagged
  beToH = fromIntegral . be16toh . fromIntegral . unTagged

instance Endian Int32 where
  hToLE = Tagged . fromIntegral . htole32 . fromIntegral
  hToBE = Tagged . fromIntegral . htobe32 . fromIntegral
  leToH = fromIntegral . le32toh . fromIntegral . unTagged
  beToH = fromIntegral . be32toh . fromIntegral . unTagged

instance Endian Int64 where
  hToLE = Tagged . fromIntegral . htole64 . fromIntegral
  hToBE = Tagged . fromIntegral . htobe64 . fromIntegral
  leToH = fromIntegral . le64toh . fromIntegral . unTagged
  beToH = fromIntegral . be64toh . fromIntegral . unTagged

-- | This instance is machine-dependent.
instance Endian CSize where
  hToLE = fmap (fromIntegral @Word) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word) . hToBE . fromIntegral
  leToH = fromIntegral @Word . beToH . fromIntegral . unTagged
  beToH = fromIntegral @Word . beToH . fromIntegral . unTagged

-- | This instance is machine-dependent.
instance Endian Word where
#if WORD_SIZE_IN_BITS == 64
  hToLE = fmap (fromIntegral @Word64) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word64) . hToBE . fromIntegral
  leToH = fromIntegral @Word64 . beToH . fromIntegral . unTagged
  beToH = fromIntegral @Word64 . beToH . fromIntegral . unTagged
#elif WORD_SIZE_IN_BITS == 32
  hToLE = fmap (fromIntegral @Word32) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word32) . hToBE . fromIntegral
  leToH = fromIntegral @Word32 . beToH . fromIntegral . unTagged
  beToH = fromIntegral @Word32 . beToH . fromIntegral . unTagged
#endif

--------------------------------------------------------------------------------

htole16, htobe16, le16toh, be16toh :: Word16 -> Word16
htole32, htobe32, le32toh, be32toh :: Word32 -> Word32
htole64, htobe64, le64toh, be64toh :: Word64 -> Word64
#ifdef WORDS_BIGENDIAN
htole16 = byteSwap16
le16toh = byteSwap16
htole32 = byteSwap32
le32toh = byteSwap32
htole64 = byteSwap64
le64toh = byteSwap64
htobe16 = id
be16toh = id
htobe32 = id
be32toh = id
htobe64 = id
be64toh = id
#else
htobe16 = byteSwap16
be16toh = byteSwap16
htobe32 = byteSwap32
be32toh = byteSwap32
htobe64 = byteSwap64
be64toh = byteSwap64
htole16 = id
le16toh = id
htole32 = id
le32toh = id
htole64 = id
le64toh = id
#endif

--------------------------------------------------------------------------------
-- | @'padLeftN' w a@ extends @a@ with zero or more @w@s on its left.
-- Returns a copy.
padLeftN
  :: forall a b
  .  ( Access a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padLeftN w a =
  unsafeAllocN_ $ \bP ->
  access a $ \aP -> do
    let bL = lengthN @b
        aL = length a
        dLi = intervalInt bL - intervalInt aL -- positive because (aL <= bL)
    c_memset bP w (fromIntegral dLi)
    c_memcpy (plusPtr bP dLi) aP (intervalCSize aL)

-- | @'padRightN' w a@ extends @a@ with zero or more @w@s on its right.
-- Returns a copy.
padRightN
  :: forall a b
  .  ( Access a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padRightN w a =
  unsafeAllocN_ $ \bP ->
  access a $ \aP -> do
    let aL = length a
        bL = lengthN @b
        dLi = intervalInt bL - intervalInt aL -- positive because (aL <= bL)
    void $ c_memcpy bP aP (intervalCSize aL)
    c_memset (plusPtr bP (intervalInt aL)) w (fromIntegral dLi)

--------------------------------------------------------------------------------

instance GetLength B.ByteString where
  type MinLength B.ByteString = 0
  type MaxLength B.ByteString = MaxInt
  length = fromMaybe (error "By.lenght: unexpected ByteString length")
         . intervalFrom
         . B.length

instance Access B.ByteString where
  access bs g = do
    let (fp, off, _len) = BI.toForeignPtr bs
    withForeignPtr fp $ \p -> g $! plusPtr p off

instance Alloc B.ByteString where
  alloc len g = do
    let len' = intervalInt len
    fp <- BI.mallocByteString len'
    a <- withForeignPtr fp (g . castPtr)
    pure (BI.fromForeignPtr fp 0 len', a)

--------------------------------------------------------------------------------

-- | Bytes suitable for storing sensitive information.
--
-- * __Memory is zeroed__ once it becomes unreachable.
-- /The bytes say “bye”. Get it? Great name./
--
-- * __Constant time 'Eq'uality__ comparisson when the compared 'Byets'
-- are of the same length.
--
-- * __Constant time 'Ord'ering__ when the compared 'Byets'
-- are of the same length.
--
-- * __Disabled 'Show' instance__ so that you don't accidentally 'Prelude.show'
-- secrets.
data Byets = Byets (LengthInterval Byets) (ForeignPtr Word8)

-- | The 'Show' instance for 'Byets' is explicitly __disabled__
-- so that you don't go showing presumably secret things.
-- If you really want this, use 'By.show' from the "By" module
-- instead of 'Prelude.show' from the "Prelude" module.
instance NoSuchInstance => Show Byets where show = undefined
type family NoSuchInstance where
  NoSuchInstance = GHC.TypeError
    ( 'GHC.Text "The " 'GHC.:<>: 'GHC.ShowType Show 'GHC.:<>:
      'GHC.Text " instance for " 'GHC.:<>: 'GHC.ShowType Byets 'GHC.:<>:
      'GHC.Text " is explicitly disabled" 'GHC.:$$:
      'GHC.Text "so that you don't go showing presumably secret things." 'GHC.:$$:
      'GHC.Text "If you really want this, use By.show " 'GHC.:<>:
      'GHC.Text "instead of Prelude.show." )

-- | Provided only as a convenience. If the 'Byets' to concatenate
-- add up to more than 'MaxInt', this 'error's. Notice that this is
-- true of types like 'B.ByteString', too. Use 'concat' if you are
-- paranoid.
instance Semigroup Byets where
  a <> b | length a == interval @0 = b
         | length b == interval @0 = a
         | otherwise = fromMaybe (error "By.Byets.(<>): too long") (append a b)

-- | See the 'Semigroup' instance for 'Byets'.
instance Monoid Byets where
  {-# NOINLINE mempty #-}
  mempty = unsafePerformIO $ do
    fp <- newForeignPtr_ nullPtr
    pure $ Byets (interval @0) fp
  mconcat []  = mempty
  mconcat [a] = a
  mconcat as  = fromMaybe (error "By.Byets.mconcat: too long") (concat as)


-- | Provided only as a convenience. While the allocated 'Byets' will be
-- zeroed once they become unreachable, the input to 'fromString' may not.
-- Also, the input 'Char's are silently truncated using 'BI.c2w' the same
-- way they are in the case of the 'IsString' instance for 'B.ByteString'.
instance IsString Byets where
  fromString = fromMaybe (error "By.Byets.fromString: too long")
             . pack . map BI.c2w

-- | __Constant time__ when the 'Byets' have the same 'length'.
-- Variable time otherwise.
instance Eq Byets where
  {-# NOINLINE (==) #-}
  a == b = unsafeDupablePerformIO $ do
    let aL = intervalCSize (length a)
        bL = intervalCSize (length b)
    access a $ \pa -> access b $ \pb ->
      pure $ if aL == bL
        then c_by_memeql_ct pa pb aL
        else 0 == c_memcmp pa pb aL

-- | __Constant time__ when the 'Byets' have the same 'length'.
-- Variable time otherwise.
instance Ord Byets where
  {-# NOINLINE compare #-}
  compare a b = unsafeDupablePerformIO $ do
    let aL = intervalCSize (length a)
        bL = intervalCSize (length b)
    access a $ \pa -> access b $ \pb ->
      pure $ if aL == bL
        then compare (c_by_memcmp_be_ct pa pb aL) 0
        else case c_memcmp pa pb aL of
               0 -> compare aL bL
               x -> compare x 0

-- | __Constant time__. A bit more efficient than the default instance.
instance {-# OVERLAPS #-} Access (Sized len Byets)
  => Eq (Sized len Byets) where
  a == b = unsafeDupablePerformIO $
    access a $ \pa ->
    access b $ \pb ->
    pure $ c_by_memeql_ct pa pb (intervalCSize (length a))

-- | __Constant time__. A bit more efficient than the default instance.
instance {-# OVERLAPS #-} Access (Sized len Byets)
  => Ord (Sized len Byets) where
  {-# NOINLINE compare #-}
  compare a b = unsafeDupablePerformIO $
    access a $ \pa ->
    access b $ \pb ->
    pure $ compare (c_by_memcmp_be_ct pa pb (intervalCSize (length a))) 0

instance GetLength Byets where
  type MinLength Byets = 0
  type MaxLength Byets = MaxInt
  length (Byets len _) = len

instance Access Byets where
  access (Byets _ fp) g = withForeignPtr fp g

-- | The allocated bytes will be automatically zeroed once they become
-- unreachable.
instance Alloc Byets where
  alloc len g = do
    fp <- Memzero.mallocForeignPtrBytes (intervalInt len)
    a <- withForeignPtr fp g
    pure (Byets len fp, a)

--------------------------------------------------------------------------------

-- | Encode @a@ as base-16. 'Nothing' if result doesn't fit in @b@.
toBase16 :: (Access a, Alloc b)
         => Bool -- Uppercase if 'True'.
         -> a
         -> Maybe b
toBase16 u = \bin -> do
    b16L <- intervalFrom (2 * intervalInteger (length bin))
    pure $ unsafeAlloc_ b16L $ \b16P ->
           access bin $ \binP ->
           f b16P binP (intervalCSize (length bin))
  where
    f = if u then c_by_to_base16_upper
             else c_by_to_base16_lower

-- | Encode @a@ as base-16. The result is known to fit in @b@.
toBase16N
 :: forall a b
 .  ( Access a
    , Alloc b
    , MinLength b <= MinLength a * 2
    , MaxLength a * 2 <= MaxLength b )
 => Bool -- Uppercase if 'True'.
 -> a
 -> b
toBase16N u = fromMaybe (error "By.toBase16N: impossible") . toBase16 u

fromBase16 :: forall a b. (Access a, Alloc b) => a -> Maybe b
fromBase16 b16 = do
  let b16L = length b16
  binL <- case divMod (intervalInt b16L) 2 of
            (d, 0) -> intervalFrom d
            _      -> Nothing
  let (bin, ret) = unsafeAlloc binL $ \binP ->
                   access b16 $ \b16P ->
                   c_by_from_base16 binP (intervalCSize binL) b16P
  guard (ret == 0)
  Just bin

--------------------------------------------------------------------------------

foreign import ccall unsafe "string.h memcpy"
  c_memcpy
    :: Ptr Word8 -- ^ dst
    -> Ptr Word8 -- ^ src
    -> CSize -- ^ len
    -> IO (Ptr Word8)

foreign import ccall unsafe "string.h memset"
  c_memset
    :: Ptr Word8 -- ^ ptr
    -> Word8 -- ^ value
    -> CSize -- ^ len
    -> IO ()

foreign import ccall unsafe "string.h memcmp"
  c_memcmp
    :: Ptr Word8 -- ^ a
    -> Ptr Word8 -- ^ b
    -> CSize -- ^ len
    -> CInt

foreign import ccall unsafe "by.h by_memeql_ct"
  c_by_memeql_ct
    :: Ptr Word8 -- ^ a
    -> Ptr Word8 -- ^ b
    -> CSize -- ^ len
    -> Bool

foreign import ccall unsafe "by.h by_memcmp_be_ct"
  c_by_memcmp_be_ct
    :: Ptr Word8 -- ^ a
    -> Ptr Word8 -- ^ b
    -> CSize -- ^ len
    -> CInt

foreign import ccall unsafe "by.h by_to_base16_lower"
  c_by_to_base16_lower
    :: Ptr Word8 -- ^ base16
    -> Ptr Word8 -- ^ bin
    -> CSize -- ^ bin_len
    -> IO ()

foreign import ccall unsafe "by.h by_to_base16_upper"
  c_by_to_base16_upper
    :: Ptr Word8 -- ^ base16
    -> Ptr Word8 -- ^ bin
    -> CSize -- ^ bin_len
    -> IO ()

foreign import ccall unsafe "by.h by_from_base16"
  c_by_from_base16
    :: Ptr Word8 -- ^ bin
    -> CSize -- ^ bin_len
    -> Ptr Word8 -- ^ base16
    -> IO CInt

--------------------------------------------------------------------------------

data Base16Impl
  = Base16Impl_Scalar
  | Base16Impl_SSSE3
  | Base16Impl_AVX2
  deriving (Eq, Ord, Show, Bounded, Enum)

-- | Currently active 'Base16Impl'.
base16Impl :: Base16Impl
base16Impl
  | _c_by_to_base16_upper == _c_by_to_base16_upper__scalar = Base16Impl_Scalar
  | _c_by_to_base16_upper == _c_by_to_base16_upper__ssse3  = Base16Impl_SSSE3
  | _c_by_to_base16_upper == _c_by_to_base16_upper__avx2   = Base16Impl_AVX2
  | otherwise = error "base16Impl: impossible"
{-# NOINLINE base16Impl #-}

foreign import ccall unsafe "by.h &by_to_base16_upper"
  _c_by_to_base16_upper :: Ptr a
foreign import ccall unsafe "by.h &by_to_base16_upper__scalar"
  _c_by_to_base16_upper__scalar :: Ptr a
foreign import ccall unsafe "by.h &by_to_base16_upper__ssse3"
  _c_by_to_base16_upper__ssse3 :: Ptr a
foreign import ccall unsafe "by.h &by_to_base16_upper__avx2"
  _c_by_to_base16_upper__avx2 :: Ptr a



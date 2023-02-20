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
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

#include <MachDeps.h>

module By {--}
  ( GetLength (..)
  , LengthInterval
  , LengthEnds

  , LengthIntervalHard
  , LengthEndsHard

  , KnownLength(..)
  , lengthN

  , Peek (..)

  , Poke
  , poke

  , Alloc (..)
  , unsafeAllocFreeze

  , allocN
  , unsafeAllocFreezeN

  , pack
  , unpack
  , shows
  , copy
  , copyN
  , replicate
  , replicateN
  , padLeftN
  , padRightN
  , appendN
  , takeN
  , dropN
  , splitAtN
  , concat

  , Sized
  , unSized
  , sized
  , unsafeSized
  , withSized
  , withSizedMinMax

  , toBase16
  , toBase16N
  , fromBase16

  , Endian(..)
  , Size

  -- * Misc
  , proveLE
  ) --}
where

import Control.Monad
import Data.ByteString qualified as B
import Data.ByteString.Internal qualified as BI
import Data.Char (chr)
import Data.Coerce
import Data.Constraint
import Data.Foldable qualified as F
import Data.Int
import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Tagged
import Data.Type.Ord (OrderingI(..))
import Data.Word
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (withForeignPtr)
import Foreign.Ptr (Ptr, nullPtr, plusPtr, castPtr)
import Foreign.Storable qualified as Sto
import GHC.TypeNats hiding (type (<=))
import Prelude hiding (concat, length, replicate, shows)
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

import Interval (type (<=))
import Interval qualified as I

--------------------------------------------------------------------------------

-- | Hard maximum length interval ends supported by this library.
-- We want 'length' to stay within 'Int' bounds since most Haskell libraries
-- use 'Int' instead of 'CSize' for counting length.
type LengthEndsHard = I.CC 0 (I.MaxBound Int)

_test_LengthEndsHard =  Dict
_test_LengthEndsHard :: Dict (LengthEndsHard `I.SubOf` I.TypeEnds CSize)

type LengthIntervalHard = I.Interval LengthEndsHard Int

-- | I.Interval endpoints for @'LengthInterval' t@.
type LengthEnds (t :: Type) = I.CC (MinLength t) (MaxLength t)

-- | The type of 'length'. Essentially, a positive interval of 'Int' counting
-- the number of bytes of user data that fit in @t@, excluding any extra bytes
-- that may be required by its structure that are not intended for user data.
type LengthInterval (t :: Type) = I.Interval (LengthEnds t) Int

-- | Superclass 'Constraint's for @'GetLength' t@.

-- TODO: some of the constraints here are redundant. Simplify if it annoys
-- downstream usage.
type GetLength' (t :: Type) =
  ( LengthEnds t `I.SubOf` LengthEndsHard
  , LengthEnds t `I.Contains` MinLength t
  , LengthEnds t `I.Contains` MaxLength t

  , I.KnownInterval (LengthEnds t) Int
  , I.KnownNum (MinLength t) Int
  , I.KnownNum (MaxLength t) Int

  , I.KnownNum (MinLength t) CSize
  , I.KnownNum (MaxLength t) CSize
  , I.KnownInterval (LengthEnds t) CSize

  , I.KnownNum (MinLength t) Natural
  , I.KnownNum (MaxLength t) Natural
  , I.KnownInterval (LengthEnds t) Natural

  , KnownNat (MinLength t)
  , KnownNat (MaxLength t)
  ) :: Constraint

-- | Runtime byte length discovery.
class GetLength' t => GetLength t where
  type MinLength (t :: Type) :: Natural
  type MaxLength (t :: Type) :: Natural
  length :: t -> LengthInterval t
  default length :: KnownLength t => t -> LengthInterval t
  length (_ :: t) = lengthN (Proxy @t)

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
lengthN :: forall t. KnownLength t => Proxy t -> LengthInterval t
lengthN _ = I.intervalVal (Proxy @(Length t))

-- | Raw byte access for read-only purposes.
--
-- __WARNING__ The “read-only” part is not enforced anywhere. Be careful.
class GetLength t => Peek t where
  peek :: t -> (Ptr p -> IO a) -> IO a

-- | Raw byte access for read-write purposes.
class Peek t => Poke t

poke :: Poke t => t -> (Ptr p -> IO a) -> IO a
poke = peek
{-# INLINE poke #-}

-- | Arbitrary byte length allocation and initialization.
class GetLength t => Alloc t where
  alloc :: LengthInterval t
        -> (Ptr p -> IO a)
        -- ^ Iitialization procedure for 'length'
        -- bytes starting at the given 'Ptr'.
        -> IO (t, a)

-- | Like 'alloc', but “pure”. This is safe as long as the
-- initialization procedure only interacts with the 'length'
-- bytes starting at the given 'Ptr'.
unsafeAllocFreeze
  :: Alloc t
  => LengthInterval t -- ^ 'length'.
  -> (Ptr p -> IO a)
  -- ^ Initialization procedure for 'length'
  -- bytes starting at the given 'Ptr'.
  -> (t, a)
unsafeAllocFreeze len g = unsafePerformIO (alloc len g)
{-# NOINLINE unsafeAllocFreeze #-}

-- | @'replicate' n x@ repeats @n@ times the byte @x@.
replicate :: Alloc a => LengthInterval a -> Word8 -> a
replicate len x = fst $ unsafeAllocFreeze len (\p -> _memset p x len)

-- | Fixed byte length allocation and initialization.
allocN :: forall t p a. (Alloc t, KnownLength t) => (Ptr p -> IO a) -> IO (t, a)
allocN = alloc (lengthN (Proxy @t))
{-# INLINE allocN #-}

-- | Like 'allocN', but “pure”. This is safe as long as the
-- initialization procedure only interacts with @'Length' t@
-- bytes starting at the given 'Ptr'.
unsafeAllocFreezeN
  :: (Alloc t, KnownLength t)
  => (Ptr p -> IO a)
  -- ^ Initialization procedure for @'Length' t@
  -- bytes starting at the given 'Ptr'.
  -> (t, a)
unsafeAllocFreezeN g = unsafePerformIO (allocN g)
{-# NOINLINE unsafeAllocFreezeN #-}

-- | @'replicate' x@ repeats @'Length' a@ times the byte @x@.
replicateN :: forall a. (Alloc a, KnownLength a) => Word8 -> a
replicateN = replicate (lengthN (Proxy @a))

-- | @'copy' a@ copies all of @a@ into a different memory address,
-- with a new type, if it fits.
{-# NOINLINE copy #-}
copy
  :: forall a b
  .  ( Peek a
     , Alloc b )
  => a
  -> Maybe b
copy a = f <$> I.downcast (length a)
  where
    {-# NOINLINE f #-}
    f bL = unsafeDupablePerformIO $
           peek a $ \aP ->
           fmap fst $ alloc bL $ \bP ->
           _memcpy bP aP bL

-- | @'copy\'' a@ copies all of @a@ into a different memory address,
-- with a new type.
{-# NOINLINE copyN #-}
copyN
  :: forall a b
  .  ( Peek a
     , Alloc b
     , LengthEnds a `I.SubOf` LengthEnds b )
  => a
  -> b
copyN a =
  let bL = length a
  in  unsafeDupablePerformIO $
      peek a $ \aP ->
      fmap fst $ alloc (I.upcast bL) $ \bP ->
      _memcpy bP aP bL

-- | @'appendN' a b@ concatenates @a@ and @b@, in that order.
appendN
  :: forall a b c
  .  ( Peek a
     , Peek b
     , Alloc c
     , KnownLength a
     , KnownLength b
     , KnownLength c
     , Length c ~ (Length a + Length b) )
  => a
  -> b
  -> c
appendN =
  let aL = lengthN (Proxy @a)
      bL = lengthN (Proxy @b)
  in \a b -> fst $ unsafeAllocFreezeN $ \cP ->
                   peek a $ \aP ->
                   peek b $ \bP -> do
                     _memcpy cP aP aL
                     _memcpy (_plusPtr cP aL) bP bL

-- | @'splitAtN' a@ splits @a@ into two parts of known lengths.
--
-- The resulting parts are copies independent from @a@.
splitAtN
  :: forall a b c
  .  ( Peek a
     , Alloc b
     , Alloc c
     , KnownLength b
     , KnownLength c
     , Length a ~ (Length b + Length c) )
  => a
  -> (b, c)
splitAtN =
  let bL = lengthN (Proxy @b)
      cL = lengthN (Proxy @c)
  in \a -> unsafeAllocFreezeN $ \bP ->
           fmap fst $ allocN $ \cP ->
           peek a $ \aP -> do
             _memcpy bP aP bL
             _memcpy cP (_plusPtr aP bL) cL

-- | @'takeN' a@ copies the leading part of @a@ of known length.
takeN
  :: forall a b.
     ( Peek a
     , Alloc b
     , KnownLength b
     , Length b <= Length a )
  => a
  -> b
takeN =
  let bL = lengthN (Proxy @b)
  in  \a -> fst $ unsafeAllocFreezeN $ \bP ->
                  peek a $ \aP ->
                  _memcpy bP aP bL

-- | @'takeN' a@ copies the trailing part of @a@ of known length.
dropN
  :: forall a b.
     ( Peek a
     , Alloc b
     , KnownLength a
     , KnownLength b
     , Length b <= Length a )
  => a
  -> b
dropN = \a ->
    fst $ unsafeAllocFreezeN $ \bP ->
          peek a $ \aP ->
          _memcpy bP (plusPtr aP pL') bL
  where
    aL = lengthN (Proxy @a)
    bL = lengthN (Proxy @b)
    pL' = I.unInterval aL - I.unInterval bL

-- | 'Nothing' if the result doesn't fit in @a@.
pack :: forall a f. (Alloc a, Foldable f) => f Word8 -> Maybe a
pack ws = do
  aL <- I.intervalFrom (F.length ws)
  pure $ fst $ unsafeAllocFreeze aL $ \aP ->
         F.foldlM (\off w -> do c_memset (plusPtr aP off) w 1
                                pure $! off + 1)
                  0
                  ws

{-# NOINLINE unpack #-}
unpack :: Peek a => a -> [Word8]
unpack a = unsafeDupablePerformIO $ peek a (f (I.unInterval' (length a)))
  where
    f :: Int -> Ptr Word8 -> IO [Word8]
    f 0 !_ = pure []
    f n  p = do !x <- Sto.peek p
                !xs <- f (n - 1) (plusPtr p 1)
                pure (x : xs)

shows :: Peek a => a -> ShowS
shows = showString . fmap (chr . fromIntegral) . unpack

-- | Concatenates all the @a@s. 'Nothing' if the result doesn't fit in @b@.
concat :: forall a b. (Peek a, Alloc b) => [a] -> Maybe b
concat as = do
  bL <- do
    -- We add lengths as 'Natural' to avoid overflowing 'Int' while adding.
    x <- I.intervalFrom $ F.sum $ fmap (I.unInterval' . length) as
    I.downcast (x :: I.Interval LengthEndsHard Natural)
  Just $ fst $ unsafeAllocFreeze bL $ \outP ->
         F.foldlM (\off a -> peek a $ \aP -> do
                      let aL = length a
                      _memcpy (plusPtr outP off) aP aL
                      pure $! off + I.unInterval' aL)
         0
         as

--------------------------------------------------------------------------------

-- | Interpreted as 'nullPtr'.
instance Peek () where
  peek _ g = g nullPtr
  {-# INLINE peek #-}

instance GetLength () where
  type MinLength () = 0
  type MaxLength () = 0
  length () = I.intervalVal (Proxy @0)

--------------------------------------------------------------------------------

newtype Sized (len :: Natural) t = Sized t
  deriving newtype (Show)

deriving newtype instance {-# OVERLAPPABLE #-} Eq t => Eq (Sized len t)
deriving newtype instance {-# OVERLAPPABLE #-} Ord t => Ord (Sized len t)

deriving newtype instance (GetLength (Sized len t), Peek t)
  => Peek (Sized len t)

deriving newtype instance (Peek (Sized len t), Poke t)
  => Poke (Sized len t)

instance GetLength' (Sized len t) => GetLength (Sized len t) where
  type MinLength (Sized len t) = len
  type MaxLength (Sized len t) = len

instance
  ( Alloc t
  , MinLength t <= len
  , len <= MaxLength t
  , KnownLength (Sized len t)
  ) => Alloc (Sized len t) where
  alloc l g = do
    (t, a) <- alloc (I.upcast l) g
    pure (Sized t, a)
  {-# INLINE alloc #-}

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
  let pLen = Proxy @len
  Dict <- proveLE (Proxy @(MinLength t)) pLen
  Dict <- proveLE pLen (Proxy @(MaxLength t))
  Dict <- proveLE pLen (Proxy @(I.MaxBound Int))
  tL :: LengthInterval t <- I.downcast (length t)
  guard (tL == I.intervalVal (Proxy @len))
  pure (Sized t)

-- | Wrap the @t@ in a 'Sized' if it has the correct length,
-- otherwise fail with 'error'.
unsafeSized
  :: forall len t
  .  (KnownNat len, GetLength t)
  => t
  -> Sized len t
unsafeSized = fromMaybe (error "unsafeSized") . sized
{-# INLINE unsafeSized #-}

withSized
  :: forall t a
  .  GetLength t
  => t
  -> (forall len
        .  KnownLength (Sized len t)
        => Sized len t
        -> a)
  -> a
withSized t g = fromMaybe (error "withSized") $
  withSizedMinMax (Proxy @(MinLength t)) (Proxy @(MaxLength t)) t g

-- | Wrap the @t@ in a 'Sized' of some unknown length
-- within @min@ and @max@.
withSizedMinMax
  :: forall min max t a
  .  ( GetLength t
     , KnownNat min
     , KnownNat max )
     -- , I.CC min max `I.SubOf` LengthEnds t )
  => Proxy min
  -> Proxy max
  -> t
  -> ( forall len
       .  ( KnownLength (Sized len t)
          , min <= len
          , len <= max )
       => Sized len t
       -> a )
  -> Maybe a
withSizedMinMax pMin pMax t g = do
  SomeNat (pLen :: Proxy len) <- pure $ someNatVal $ I.unInterval' (length t)
  Dict <- proveLE pMin pLen
  Dict <- proveLE pLen pMax
  Dict <- proveLE (Proxy @0) pLen
  Dict <- proveLE pLen (Proxy @(I.MaxBound Int))
  Dict <- proveLE pLen (Proxy @(I.MaxBound CSize))
  pure $ g (Sized t :: Sized len t)

proveLE
  :: (KnownNat l, KnownNat r)
  => Proxy l
  -> Proxy r
  -> Maybe (Dict (l <= r))
proveLE l r = case cmpNat l r of
  EQI -> Just $ unsafeCoerce (Dict @(0 <= 0))
  LTI -> Just $ unsafeCoerce (Dict @(0 <= 1))
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
type instance Size Int  = Size Int64
type instance Size Word = Size Word64
#elif WORD_SIZE_IN_BITS == 32
type instance Size Int  = Size Int32
type instance Size Word = Size Word32
#else
#  error "Unexpected WORD_SIZE_IN_BYTES"
#endif

--------------------------------------------------------------------------------

-- | Conversion between host byte encoding and Little-Endian or
-- Big-Endian byte encoding.
class I.KnownNum (Size a) Int => Endian a where
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
  encodeH :: forall h. (Alloc h, LengthEnds h `I.Contains` Size a) => a -> h
  -- | Default implementation in case there is a @'Sto.Storable' a@ instance.
  default encodeH
    :: forall h
    .  ( Alloc h
       , LengthEnds h `I.Contains` Size a
       , Sto.Storable a )
    => a -> h
  encodeH = fst
          . unsafeAllocFreeze (I.intervalVal (Proxy @(Size a)))
          . flip Sto.poke

  -- | Writes @a@ in @le@ using Litle-Endian encoding.
  encodeLE :: forall le. (Alloc le, LengthEnds le `I.Contains` Size a) => a -> le
  encodeLE = encodeH . unTagged . hToLE

  -- | Writes @a@ in @be@ using Big-Endian encoding.
  encodeBE
    :: forall be. (Alloc be, LengthEnds be `I.Contains` Size a) => a -> be
  encodeBE = encodeH . unTagged . hToBE

  -- | Reads @a@ from @h@ using the host encoding.
  decodeH :: forall h. (Peek h, Size a ~ Length h) => h -> a
  -- | Default implementation in case there is a @'Sto.Storable' a@ instance.
  default decodeH
    :: forall h. (Peek h, Size a ~ Length h, Sto.Storable a) => h -> a
  decodeH h = unsafeDupablePerformIO $ peek h Sto.peek
  {-# NOINLINE decodeH #-}

  -- | Reads @a@ from @le@ using Little-Endian encoding.
  decodeLE :: forall le. (Peek le, Size a ~ Length le) => le -> a
  decodeLE = leToH . Tagged . decodeH

  -- | Reads @a@ from @be@ using Big-Endian encoding.
  decodeBE :: forall be. (Peek be, Size a ~ Length be) => be -> a
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

instance Endian CSize where
  hToLE = fmap (fromIntegral @Word) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word) . hToBE . fromIntegral
  leToH = fromIntegral @Word . beToH . fromIntegral . unTagged
  beToH = fromIntegral @Word . beToH . fromIntegral . unTagged

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
  .  ( Peek a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padLeftN w a =
  fst $
  unsafeAllocFreezeN $ \bP ->
  peek a $ \aP -> do
    let bLi :: Int   = I.unInterval (lengthN (Proxy @b))
        aLi :: Int   = I.unInterval (length a)
        dLi :: Int   = bLi - aLi -- no overflow because (aLs <= bLi)
        dLs :: CSize = fromIntegral dLi -- safe because LengthEndsHard
    c_memset bP w dLs
    c_memcpy (plusPtr bP dLi) aP (I.unInterval' (length a))

-- | @'padRightN' w a@ extends @a@ with zero or more @w@s on its right.
-- Returns a copy.
padRightN
  :: forall a b
  .  ( Peek a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padRightN w a =
  fst $
  unsafeAllocFreezeN $ \bP ->
  peek a $ \aP -> do
    let bLi :: Int   = I.unInterval (lengthN (Proxy @b))
        aLi :: Int   = I.unInterval (length a)
        dLi :: Int   = bLi - aLi -- no overflow because (aLs <= bLi)
        dLs :: CSize = fromIntegral dLi -- safe because LengthEndsHard
    void $ c_memcpy bP aP (I.unInterval' (length a))
    c_memset (plusPtr bP aLi) w dLs

--------------------------------------------------------------------------------

instance GetLength B.ByteString where
  type MinLength B.ByteString = 0
  type MaxLength B.ByteString = I.MaxBound Int
  length = fromMaybe (error "By.lenght: unsupported ByteString length")
         . I.intervalFrom
         . B.length

instance Peek B.ByteString where
  peek bs g = do
    let (fp, off, _len) = BI.toForeignPtr bs
    withForeignPtr fp $ \p -> g $! plusPtr p off

instance Alloc B.ByteString where
  alloc len g = do
    let len' = I.unInterval len
    fp <- BI.mallocByteString len'
    a <- withForeignPtr fp (g . castPtr)
    pure (BI.fromForeignPtr fp 0 len', a)

--------------------------------------------------------------------------------

-- | Like 'c_memcpy', except it takes an 'Interval' so as to avoid having
-- to litter the calling code with 'I.unInterval'.
_memcpy
  :: I.Upcast LengthEndsHard CSize e a
  => Ptr Word8 -- ^ dst
  -> Ptr Word8 -- ^ src
  -> I.Interval e a
  -> IO ()
_memcpy dst src len =
  void $ c_memcpy dst src
       $ I.unInterval (I.upcast len :: I.Interval LengthEndsHard CSize)

-- | Like 'c_memset', except it takes an 'Interval' so as to avoid having
-- to litter the calling code with 'I.unInterval'.
_memset
  :: I.Upcast LengthEndsHard CSize e a
  => Ptr Word8 -- ^ dst
  -> Word8     -- ^ value
  -> I.Interval e a
  -> IO ()
_memset dst value len =
  c_memset dst value $
    I.unInterval (I.upcast len :: I.Interval LengthEndsHard CSize)

-- | Like 'plusPtr', except it takes an 'Interval' so as to avoid having
-- to litter the calling code with 'I.unInterval'.
_plusPtr
  :: I.Upcast (I.TypeEnds Int) Int e a
  => Ptr x -- ^ ptr
  -> I.Interval e a -- ^ diff
  -> Ptr x
_plusPtr p d = plusPtr p (I.unInterval' (I.upcast d :: I.TypeInterval Int))

--------------------------------------------------------------------------------

-- | Encode @a@ as base-16. 'Nothing' if result doesn't fit in @b@.
toBase16 :: (Peek a, Alloc b) => a -> Maybe b
toBase16 = \bin -> do
  b16L <- I.intervalFrom' (I.unInterval' (length bin) * 2 :: Integer)
  pure $ fst $ unsafeAllocFreeze b16L $ \b16P ->
         peek bin $ \binP -> do
           ret <- c_by_to_base16 b16P (I.unInterval' b16L) binP
           when (ret /= 0) $ fail "toBase16: unexpected internal error"

-- | Encode @a@ as base-16. The result is known to fit in @b@.
toBase16N
 :: forall a b
 .  ( Peek a
    , Alloc b
    , MinLength b <= MinLength a GHC.TypeNats.* 2
    , MaxLength a GHC.TypeNats.* 2 <= MaxLength b )
 => a
 -> b
toBase16N = fromMaybe (error "toBase16N: impossible") . toBase16

fromBase16 :: forall a b. (Peek a, Alloc b) => a -> Maybe b
fromBase16 b16 = do
  let b16L = length b16
  binL <- case divMod (I.unInterval b16L) 2 of
            (d, 0) -> I.intervalFrom d
            _      -> Nothing
  let (bin, ret) = unsafeAllocFreeze binL $ \binP ->
                   peek b16 $ \b16P ->
                   c_by_from_base16 binP b16P (I.unInterval' b16L)
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

foreign import ccall unsafe "by.h by_to_base16"
  c_by_to_base16
    :: Ptr Word8 -- ^ base16
    -> CSize -- ^ base16_len
    -> Ptr Word8 -- ^ bin
    -> IO CInt

foreign import ccall unsafe "by.h by_from_base16"
  c_by_from_base16
    :: Ptr Word8 -- ^ bin
    -> Ptr Word8 -- ^ base16
    -> CSize -- ^ base16_len
    -> IO CInt

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
  , unsafeAllocFreeze
  , allocN
  , unsafeAllocFreezeN

    -- * Peek & Poke
  , Peek (..)
  , Poke
  , poke

    -- * Sized
  , Sized
  , unSized
  , sized
  , unsafeSized
  , withSized
  , withSizedMinMax
  , withSizedMinMaxN

    -- * Base16
  , toBase16
  , toBase16N
  , fromBase16


    -- * Utils
  , pack
  , unpack
  , shows
  , showsBase16N
  , copy
  , copyN
  , replicate
  , replicateN
  , padLeftN
  , padRightN
  , append
  , takeN
  , dropN
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
import Data.Proxy
import Data.Tagged
import Data.Type.Ord
import Data.Void
import Data.Word
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.ForeignPtr (withForeignPtr)
import Foreign.Ptr (Ptr, nullPtr, plusPtr, castPtr)
import Foreign.Storable qualified as Sto
import GHC.TypeNats
import Prelude hiding (concat, length, replicate, shows)
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

-- | Type-level version of @'maxBound' :: 'Int'@. This value is machine-dependent.
type MaxInt = Div (2 ^ (Size Int * 8)) 2 - 1

-- | An natural number known to be at least @l@, at most @r@.
--
-- * Construct safely with 'interval', 'intervalFrom', 'intervalUpcast' or
-- 'intervalDowncast'.
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

-- | The returned number is at least @l@, at most @r@.
intervalInt :: Interval l r -> Int
intervalInt = coerce

-- | The returned number is at least @l@, at most @r@.
intervalCSize :: Interval l r -> CSize
intervalCSize = fromIntegral . intervalInt

-- | The returned number is at least @l@, at most @r@.
intervalInteger :: Interval l r -> Integer
intervalInteger = fromIntegral . intervalInt

-- | The returned number is at least @l@, at most @r@.
intervalNatural :: Interval l r -> Natural
intervalNatural = fromIntegral . intervalInt

interval
  :: forall n l r
  .  (KnownNat n, l <= n, n <= r, r <= MaxInt)
  => Interval l r
interval = UnsafeInterval (fromIntegral (natVal (Proxy @n)))

intervalMin
  :: forall l r
  .  (KnownNat l, l <= r, r <= By.MaxInt)
  => By.Interval l r
intervalMin = By.interval @l

intervalMax
  :: forall l r
  .  (KnownNat r, l <= r, r <= By.MaxInt)
  => By.Interval l r
intervalMax = By.interval @r

intervalSingle
  :: forall n
  .  (KnownNat n, n <= By.MaxInt)
  => By.Interval n n
intervalSingle = By.interval @n

intervalFrom
  :: forall n l r
  .  (Integral n, KnownNat l, KnownNat r)
  => n
  -> Maybe (Interval l r)
intervalFrom = \i -> do
    let n :: Natural = fromIntegral i
    -- We check (l <= r) and (r <= z) here so as to keep constraints simpler.
    guard (l <= n && n <= r && r <= z)
    pure (UnsafeInterval (fromIntegral i))
  where
    l = natVal (Proxy @l)
    r = natVal (Proxy @r)
    z = natVal (Proxy @MaxInt)

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
replicate len x = fst $ unsafeAllocFreeze len $ \p ->
                        c_memset p x (intervalCSize len)

-- | Fixed byte length allocation and initialization.
allocN :: forall t p a. (Alloc t, KnownLength t) => (Ptr p -> IO a) -> IO (t, a)
allocN = alloc (lengthN @t)

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
replicateN = replicate (lengthN @a)

-- | @'copy' a@ copies all of @a@ into a different memory address, if it fits.
copy :: forall a b. (Peek a, Alloc b) => a -> Maybe b
copy a = do
   bL <- intervalDowncast (length a)
   pure $ fst $
          unsafeAllocFreeze bL $ \bP ->
          peek a $ \aP ->
          c_memcpy bP aP (intervalCSize bL)

-- | @'copyN' a@ copies all of @a@ into a different memory address.
copyN
  :: forall a b
  .  ( Peek a
     , Alloc b
     , MinLength b <= MinLength a
     , MaxLength a <= MaxLength b )
  => a
  -> b
copyN a =
  let aL = length a
  in  fst $ unsafeAllocFreeze (intervalUpcast aL) $ \bP ->
      peek a $ \aP ->
      c_memcpy bP aP (intervalCSize aL)


-- | @'append' a b@ concatenates @a@ and @b@, in that order.
append
  :: forall a b c
  .  ( Peek a
     , Peek b
     , Alloc c
     , MinLength c <= MinLength a + MinLength b
     , MaxLength a + MaxLength b <= MaxLength c )
  => a
  -> b
  -> c
append a b =
    fst $
    unsafeAllocFreeze cL $ \cP ->
    peek a $ \aP ->
    peek b $ \bP -> do
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
  let bL = lengthN @b
      cL = lengthN @c
  in \a -> unsafeAllocFreezeN $ \bP ->
           fmap fst $ allocN $ \cP ->
           peek a $ \aP -> do
             void $ c_memcpy bP aP (intervalCSize bL)
             c_memcpy cP (plusPtr aP (intervalInt bL)) (intervalCSize cL)

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
  let bL = lengthN @b
  in  \a -> fst $ unsafeAllocFreezeN $ \bP ->
                  peek a $ \aP ->
                  c_memcpy bP aP (intervalCSize bL)

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
          c_memcpy bP (plusPtr aP pL') (intervalCSize bL)
  where
    aL = lengthN @a
    bL = lengthN @b
    pL' = intervalInt aL - intervalInt bL

-- | 'Nothing' if the result doesn't fit in @a@.
pack :: forall a f. (Alloc a, Foldable f) => f Word8 -> Maybe a
pack ws = do
  aL <- intervalFrom (F.length ws)
  pure $ fst $ unsafeAllocFreeze aL $ \aP ->
         F.foldlM (\off w -> do c_memset (plusPtr aP off) w 1
                                pure $! off + 1)
                  0
                  ws

{-# NOINLINE unpack #-}
unpack :: Peek a => a -> [Word8]
unpack a = unsafeDupablePerformIO $ peek a (f (intervalInt (length a)))
  where
    f :: Int -> Ptr Word8 -> IO [Word8]
    f 0 !_ = pure []
    f n  p = do !x <- Sto.peek p
                !xs <- f (n - 1) (plusPtr p 1)
                pure (x : xs)

-- | Renders @a@ as a literal 'String'.
shows :: Peek a => a -> ShowS
shows = showString . fmap (chr . fromIntegral) . unpack

-- | Encodes @a@ using Base-16 encoding and then renders it as a 'String'.
showsBase16N :: forall a. (Peek a, MaxLength a * 2 <= MaxInt) => a -> ShowS
showsBase16N = case zeroLe @(MinLength a * 2) of
    Dict -> shows @B.ByteString . toBase16N

-- | Concatenates all the @a@s. 'Nothing' if the result doesn't fit in @b@.
concat :: forall a b. (Peek a, Alloc b) => [a] -> Maybe b
concat as = do
  -- We add lengths as 'Integer' to avoid overflowing 'Int' while adding.
  bL <- intervalFrom $ F.sum $ fmap (intervalInteger . length) as
  Just $ fst $ unsafeAllocFreeze bL $ \outP ->
         F.foldlM (\off a -> peek a $ \aP -> do
                      let aL = length a
                      void $ c_memcpy (plusPtr outP off) aP (intervalCSize aL)
                      pure $! off + intervalInt aL)
         0
         as

--------------------------------------------------------------------------------

-- | Interpreted as 'nullPtr'.
instance Peek () where
  peek _ g = g nullPtr

instance GetLength () where
  type MinLength () = 0
  type MaxLength () = 0
  length () = interval @0

--------------------------------------------------------------------------------

newtype Sized (len :: Natural) t = Sized t
  deriving newtype (Show)

deriving newtype instance {-# OVERLAPPABLE #-} Eq t => Eq (Sized len t)
deriving newtype instance {-# OVERLAPPABLE #-} Ord t => Ord (Sized len t)

deriving newtype instance (GetLength (Sized len t), Peek t)
  => Peek (Sized len t)

deriving newtype instance (Peek (Sized len t), Poke t)
  => Poke (Sized len t)

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
  -- | Default implementation in case there is a @'Sto.Storable' a@ instance.
  default encodeH
    :: forall h
    .  (Alloc h, MinLength h <= Size a, Size a <= MaxLength h, Sto.Storable a)
    => a -> h
  encodeH = fst
          . unsafeAllocFreeze (interval @(Size a))
          . flip Sto.poke

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
    let bL = lengthN @b
        aL = length a
        dLi = intervalInt bL - intervalInt aL -- positive because (aL <= bL)
    c_memset bP w (fromIntegral dLi)
    c_memcpy (plusPtr bP dLi) aP (intervalCSize aL)

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

instance Peek B.ByteString where
  peek bs g = do
    let (fp, off, _len) = BI.toForeignPtr bs
    withForeignPtr fp $ \p -> g $! plusPtr p off

instance Alloc B.ByteString where
  alloc len g = do
    let len' = intervalInt len
    fp <- BI.mallocByteString len'
    a <- withForeignPtr fp (g . castPtr)
    pure (BI.fromForeignPtr fp 0 len', a)

--------------------------------------------------------------------------------

-- | Encode @a@ as base-16. 'Nothing' if result doesn't fit in @b@.
toBase16 :: (Peek a, Alloc b) => a -> Maybe b
toBase16 = \bin -> do
  b16L <- intervalFrom (2 * intervalInteger (length bin))
  pure $ fst $ unsafeAllocFreeze b16L $ \b16P ->
         peek bin $ \binP -> do
           ret <- c_by_to_base16 b16P (intervalCSize b16L) binP
           when (ret /= 0) $ fail "By.toBase16: unexpected internal error"

-- | Encode @a@ as base-16. The result is known to fit in @b@.
toBase16N
 :: forall a b
 .  ( Peek a
    , Alloc b
    , MinLength b <= MinLength a * 2
    , MaxLength a * 2 <= MaxLength b )
 => a
 -> b
toBase16N = fromMaybe (error "By.toBase16N: impossible") . toBase16

fromBase16 :: forall a b. (Peek a, Alloc b) => a -> Maybe b
fromBase16 b16 = do
  let b16L = length b16
  binL <- case divMod (intervalInt b16L) 2 of
            (d, 0) -> intervalFrom d
            _      -> Nothing
  let (bin, ret) = unsafeAllocFreeze binL $ \binP ->
                   peek b16 $ \b16P ->
                   c_by_from_base16 binP b16P (intervalCSize b16L)
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

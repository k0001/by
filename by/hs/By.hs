module By
  ( GetLength (..)

  , KnownLength (..)

  , Peek (..)

  , Poke
  , poke

  , Alloc (..)
  , allocFreeze

  , AllocN (..)
  , allocFreezeN

  , Convert (..)
  , ConvertN (..)

  , pack
  , packN
  , copy
  , copyFreeze
  , copyN
  , copyFreezeN
  , replicate
  , replicateN
  , padLeftN
  , padRightN
  , appendN
  , takeN
  , dropN
  , splitAtN 

  , Sized
  , unSized
  , sized
  , unsafeSized
  , withSized
  , withSizedMax
  , withSizedMinMax

  , toBase16
  , fromBase16
  , fromBase16N

  , ByeString (..)

  , fromWord8
  , fromWord16le
  , fromWord16be
  , fromWord32le
  , fromWord32be
  , fromWord64le
  , fromWord64be

  , toWord8
  , toWord16le
  , toWord16be
  , toWord32le
  , toWord32be
  , toWord64le
  , toWord64be
  )
where

import Control.Exception (onException)
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Internal as BI
import Data.Coerce
import qualified Data.Foldable as F
import Data.Int
import Data.Proxy
import Data.String (IsString (..))
import Data.Word
import Foreign.C.Types (CInt (..), CSize (..))
import qualified Foreign.Concurrent as FC
import Foreign.ForeignPtr (mallocForeignPtrBytes, touchForeignPtr, 
                           withForeignPtr)
import Foreign.ForeignPtr.Unsafe (unsafeForeignPtrToPtr)
import Foreign.Ptr (Ptr, nullPtr, plusPtr, castPtr)
import qualified Foreign.Storable as Sto
import GHC.TypeLits
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (concat, length, replicate)

--------------------------------------------------------------------------------

-- | Runtime byte length discovery.
class GetLength t where
  length :: t -> Int
  default length :: KnownLength t => t -> Int
  length (_ :: t) = fromIntegral (natVal (Proxy @(Length t)))
  {-# INLINE length #-}

-- | Static byte length knownledge.
class (GetLength t, KnownNat (Length t)) => KnownLength t where
  type Length t :: Nat

-- | Raw byte access for read-only purposes.
--
-- **WARNING** The “read-only” part is not enforced anywhere. Be careful.
class GetLength t => Peek t where
  peek :: t -> (Ptr p -> IO a) -> IO a

-- | Raw byte access for read-write purposes.
class Peek t => Poke t

poke :: Poke t => t -> (Ptr p -> IO a) -> IO a
poke = peek
{-# INLINE poke #-}

-- | Arbitrary byte length allocation and initialization.
class (GetLength t, Monoid t) => Alloc t where
  alloc :: Int -> (Ptr p -> IO a) -> IO (t, a)

-- Like 'alloc'.
allocFreeze :: Alloc t => Int -> (Ptr p -> IO a) -> (t, a)
allocFreeze len g = unsafePerformIO (alloc len g)
{-# NOINLINE allocFreeze #-}

replicate :: forall a. Alloc a => Int -> Word8 -> a
replicate len x = fst $ allocFreeze len (\p -> _memset p len x)
{-# INLINE replicate #-}

-- | Fixed byte length allocation and initialization.
class KnownLength t => AllocN t where
  allocN :: (Ptr p -> IO a) -> IO (t, a)

-- | Like 'allocN'.
allocFreezeN :: AllocN t => (Ptr p -> IO a) -> (t, a)
allocFreezeN g = unsafePerformIO (allocN g)
{-# NOINLINE allocFreezeN #-}

replicateN :: forall a. AllocN a => Word8 -> a
replicateN x =
  let len = fromIntegral (natVal (Proxy @(Length a)))
   in fst $ allocFreezeN (\p -> _memset p len x)
{-# INLINE replicateN #-}

class (Peek a, Alloc b) => Convert a b where
  -- | Convert @a@ to @b@. The default implementation uses 'coerce' if possible.
  convert :: a -> b
  default convert :: Coercible a b => a -> b
  convert = coerce
  {-# INLINE convert #-}

-- | Fallback instance that copies @a@. 
-- Override with something more efficient if desired.
instance {-# OVERLAPPABLE #-} (Peek a, Alloc b) => Convert a b where
  convert a = fst $ copyFreeze a $ const (pure ())
  {-# INLINE convert #-}

-- | Identity.
instance (Peek a, Alloc a) => Convert a a where
  convert = id
  {-# INLINE convert #-}

class (Peek a, AllocN b, Length a ~ Length b) => ConvertN a b where
  -- | Convert @a@ to @b@. The default implementation uses 'coerce' if possible.
  convertN :: a -> b
  default convertN :: Coercible a b => a -> b
  convertN = coerce
  {-# INLINE convertN #-}

-- | Fallback instance that copies @a@. 
-- Override with something more efficient if desired.
instance {-# OVERLAPPABLE #-} (Peek a, AllocN b, KnownLength a, Length a ~ Length b) 
  => ConvertN a b where
  convertN a = fst $ copyFreezeN a $ const (pure ())
  {-# INLINE convertN #-}

-- | Identity.
instance (Peek a, AllocN a) => ConvertN a a where
  convertN = id
  {-# INLINE convertN #-}

copy :: (Peek a, Alloc b) => a -> (Ptr p -> IO x) -> IO (b, x)
copy a g = peek a $ \aP -> do
  alloc (length a) $ \bP -> do
    BI.memcpy bP aP (length a)
    g (castPtr bP)

copyFreeze :: (Peek a, Alloc b) => a -> (Ptr p -> IO x) -> (b, x)
copyFreeze a g = unsafePerformIO (copy a g)
{-# NOINLINE copyFreeze #-}

copyN
  :: (Peek a, AllocN b, KnownLength a, Length a ~ Length b)
  => a
  -> (Ptr p -> IO x)
  -> IO (b, x)
copyN a g = peek a $ \aP -> do
  allocN $ \bP -> do
    BI.memcpy bP aP (length a)
    g (castPtr bP)

copyFreezeN
  :: (Peek a, AllocN b, KnownLength a, Length a ~ Length b)
  => a
  -> (Ptr p -> IO x)
  -> (b, x)
copyFreezeN a g = unsafePerformIO (copyN a g)
{-# NOINLINE copyFreezeN #-}

-- | @'appendN' a b@ concatenates @a@ and @b@, in that order.
appendN
  :: ( Peek a
     , Peek b
     , KnownLength a
     , KnownLength b
     , AllocN c
     , Length c ~ (Length a + Length b)
     )
  => a
  -> b
  -> c
appendN a b =
  fst $
    allocFreezeN $ \cP ->
      peek a $ \aP ->
        peek b $ \bP -> do
          BI.memcpy cP aP (length a)
          BI.memcpy (plusPtr cP (length a)) bP (length b)

-- | @'splitAtN' a@ splits @a@ into two parts of known lengths. 
--
-- The resulting parts are copies independent from @a@.
splitAtN 
  :: forall a b c.
     ( Peek a
     , KnownLength a
     , AllocN b
     , AllocN c
     , Length a ~ (Length b + Length c)
     )
  => a -> (b, c)
splitAtN a = 
  let bL :: Int = fromIntegral (natVal (Proxy @(Length b)))
      cL :: Int = fromIntegral (natVal (Proxy @(Length c)))
  in allocFreezeN $ \bP ->
      fmap fst $ allocN $ \cP ->
        peek a $ \aP -> do
          BI.memcpy bP aP bL
          BI.memcpy cP (plusPtr aP bL) cL
  
-- | @'takeN' a@ copies the leading part of @a@ of known length.
takeN
  :: forall a b.
     ( Peek a
     , KnownLength a
     , AllocN b
     , Length b <= Length a)
  => a -> b
takeN a = 
  let bL :: Int = fromIntegral (natVal (Proxy @(Length b)))
  in  fst $ allocFreezeN $ \bP ->
        peek a $ \aP -> do
          BI.memcpy bP aP bL

-- | @'takeN' a@ copies the trailing part of @a@ of known length.
dropN
  :: forall a b.
     ( Peek a
     , KnownLength a
     , AllocN b
     , Length b <= Length a)
  => a -> b
dropN a = 
  let bL :: Int = fromIntegral (natVal (Proxy @(Length b)))
  in  fst $ allocFreezeN $ \bP ->
        peek a $ \aP -> do
          BI.memcpy bP (plusPtr aP (length a - bL)) bL

pack
  :: forall a f.
     ( Alloc a
     , Foldable f
     )
  => f Word8
  -> a
pack ws =
  fst $ allocFreeze (F.length ws) $ \aP -> 
    F.foldlM (\off w -> do _memset (plusPtr aP off) 1 w 
                           pure $! off + 1)
             0
             ws

packN 
  :: forall a f.
     ( AllocN a
     , Foldable f
     )
  => f Word8
  -> Maybe a
packN ws = do
  let aL :: Int = fromIntegral (natVal (Proxy @(Length a)))
  guard (F.length ws == aL)
  pure $ fst $ allocFreezeN $ \aP -> 
    F.foldlM (\off w -> do _memset (plusPtr aP off) 1 w 
                           pure $! off + 1)
             0
             ws

--------------------------------------------------------------------------------

-- | Interpreted as 'nullPtr'.
instance Peek () where
  peek _ g = g nullPtr
  {-# INLINE peek #-}

instance GetLength ()

instance KnownLength () where
  type Length () = 0

--------------------------------------------------------------------------------

newtype Sized (len :: Nat) t = Sized t
  deriving newtype (Eq, Ord, Show, Peek, Poke)

unSized :: Sized len t -> t
unSized (Sized t) = t
{-# INLINE unSized #-}

sized :: forall len t. (KnownNat len, GetLength t) => t -> Maybe (Sized len t)
sized t = do
  guard (length t == fromIntegral (natVal (Proxy @len)))
  pure (Sized t)
{-# INLINE sized #-}

-- | Construct a 'Sized' if the given @t@ has the correct length, otherwise
-- fail with 'error'. The given 'String' will be included in the error messsge.
unsafeSized 
  :: forall len t. (KnownNat len, GetLength t) => String -> t -> Sized len t
unsafeSized p = \t ->
  let tL = length t
   in case e == tL of
        True -> Sized t
        False -> error (m <> show tL)
  where
    e :: Int
    e = fromIntegral (natVal (Proxy @len))
    m :: String
    m = "unsafeSized [" <> p <> "] expected " <> show e <> " bytes, got "
{-# INLINE unsafeSized #-}

withSized
  :: forall t a.
  GetLength t
  => t
  -> (forall len. KnownNat len => Sized len t -> a)
  -> a
withSized t g = case someNatVal (toInteger (length t)) of
  Just (SomeNat (_ :: Proxy len)) -> g (Sized t :: Sized len t)
  Nothing -> undefined -- impossible, always non-negative
{-# INLINE withSized #-}

withSizedMax
  :: forall max t a.
  (GetLength t, KnownNat max)
  => Proxy max
  -> t
  -> ( forall len.
       (KnownNat len, 0 <= len, len <= max)
       => Sized len t
       -> a
     )
  -> Maybe a
withSizedMax = withSizedMinMax (Proxy @0)
{-# INLINE withSizedMax #-}

withSizedMinMax
  :: forall min max t a.
  (GetLength t, KnownNat min, KnownNat max)
  => Proxy min
  -> Proxy max
  -> t
  -> ( forall len.
       (KnownNat len, min <= len, len <= max)
       => Sized len t
       -> a
     )
  -> Maybe a
withSizedMinMax pMin pMax t g = do
  let len = toInteger (length t)
  guard (natVal pMin <= len && len <= natVal pMax)
  SomeNat (_ :: Proxy len) <- someNatVal len
  -- 'len' is between 'min' and 'max', we create a fake Dict to please 'g'.
  case unsafeCoerce (Dict :: Dict (1 <= 2, 3 <= 4)) of
    (Dict :: Dict (min <= len, len <= max)) ->
      Just (g (Sized t :: Sized len t))
{-# INLINE withSizedMinMax #-}

instance KnownNat len => KnownLength (Sized len t) where
  type Length (Sized len t) = len

instance KnownNat len => GetLength (Sized len t)

instance (KnownNat len, Alloc t) => AllocN (Sized len t) where
  allocN g = do
    (t, a) <- alloc (fromIntegral (natVal (Proxy @len))) g
    pure (Sized t, a)

instance (KnownNat len, Peek t, Alloc t) => Convert (Sized len t) t where
  convert = unSized
  {-# INLINE convert #-}

instance {-# OVERLAPPABLE #-} (KnownNat len, Convert a b) => Convert (Sized len a) b where
  convert = convert . unSized
  {-# INLINE convert #-}

instance (KnownNat len, Convert a b) => ConvertN (Sized len a) (Sized len b) where
  convertN = Sized . convert . unSized
  {-# INLINE convertN #-}

--------------------------------------------------------------------------------
-- Conversion to integer types

{-# NOINLINE toWord8 #-}
toWord8 :: (Peek a, KnownLength a, Length a ~ 1) => a -> Word8
toWord8 x = unsafeDupablePerformIO $ peek x Sto.peek

{-# NOINLINE toWord16le #-}
toWord16le :: (Peek a, KnownLength a, Length a ~ 2) => a -> Word16
toWord16le x = unsafeDupablePerformIO $ peek x (pure . c_by_load16le)

{-# NOINLINE toWord16be #-}
toWord16be :: (Peek a, KnownLength a, Length a ~ 2) => a -> Word16
toWord16be x = unsafeDupablePerformIO $ peek x (pure . c_by_load16be)

{-# NOINLINE toWord32le #-}
toWord32le :: (Peek a, KnownLength a, Length a ~ 4) => a -> Word32
toWord32le x = unsafeDupablePerformIO $ peek x (pure . c_by_load32le)

{-# NOINLINE toWord32be #-}
toWord32be :: (Peek a, KnownLength a, Length a ~ 4) => a -> Word32
toWord32be x = unsafeDupablePerformIO $ peek x (pure . c_by_load32be)

{-# NOINLINE toWord64le #-}
toWord64le :: (Peek a, KnownLength a, Length a ~ 8) => a -> Word64
toWord64le x = unsafeDupablePerformIO $ peek x (pure . c_by_load64le)

{-# NOINLINE toWord64be #-}
toWord64be :: (Peek a, KnownLength a, Length a ~ 8) => a -> Word64
toWord64be x = unsafeDupablePerformIO $ peek x (pure . c_by_load64be)

--------------------------------------------------------------------------------
-- Conversion from integer types

{-# NOINLINE fromWord8 #-}
fromWord8 :: (AllocN a, Length a ~ 1) => Word8 -> a
fromWord8 = unsafeDupablePerformIO . fmap fst . allocN . flip Sto.poke

{-# NOINLINE fromWord16le #-}
fromWord16le :: (AllocN a, Length a ~ 2) => Word16 -> a
fromWord16le = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store16le

{-# NOINLINE fromWord16be #-}
fromWord16be :: (AllocN a, Length a ~ 2) => Word16 -> a
fromWord16be = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store16be

{-# NOINLINE fromWord32le #-}
fromWord32le :: (AllocN a, Length a ~ 4) => Word32 -> a
fromWord32le = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store32le

{-# NOINLINE fromWord32be #-}
fromWord32be :: (AllocN a, Length a ~ 4) => Word32 -> a
fromWord32be = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store32be

{-# NOINLINE fromWord64le #-}
fromWord64le :: (AllocN a, Length a ~ 8) => Word64 -> a
fromWord64le = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store64le

{-# NOINLINE fromWord64be #-}
fromWord64be :: (AllocN a, Length a ~ 8) => Word64 -> a
fromWord64be = unsafeDupablePerformIO . fmap fst . allocN . flip c_by_store64be

--------------------------------------------------------------------------------

-- | @'padLeftN' w a@ extends @a@ with zero or more @w@s on its left.
-- Returns a copy.
padLeftN
  :: forall a b.
  (Peek a, KnownLength a, AllocN b, Length a <= Length b)
  => Word8
  -> a
  -> b
padLeftN w a = do
  fst $
    allocFreezeN $ \bP ->
      peek a $ \aP -> do
        _memset bP pL w
        BI.memcpy (plusPtr bP pL) aP aL
  where
    aL :: Int = fromIntegral (natVal (Proxy @(Length a)))
    bL :: Int = fromIntegral (natVal (Proxy @(Length b)))
    pL :: Int = bL - aL

-- | @'padRightN' w a@ extends @a@ with zero or more @w@s on its right.
-- Returns a copy.
padRightN
  :: forall a b.
  (Peek a, KnownLength a, AllocN b, Length a <= Length b)
  => Word8
  -> a
  -> b
padRightN w a = do
  fst $
    allocFreezeN $ \bP ->
      peek a $ \aP -> do
        BI.memcpy bP aP aL
        _memset (plusPtr bP aL) pL w
  where
    aL :: Int = fromIntegral (natVal (Proxy @(Length a)))
    bL :: Int = fromIntegral (natVal (Proxy @(Length b)))
    pL :: Int = bL - aL

--------------------------------------------------------------------------------

instance GetLength B.ByteString where
  length = B.length
  {-# INLINE length #-}

instance Peek B.ByteString where
  peek bs g = do
    let (fp, off, _len) = BI.toForeignPtr bs
    withForeignPtr fp $ \p -> g $! plusPtr p off

instance Alloc B.ByteString where
  alloc len g = do
    fp <- BI.mallocByteString len
    a <- withForeignPtr fp (g . castPtr)
    pure (BI.fromForeignPtr fp 0 len, a)

--------------------------------------------------------------------------------

-- | A 'ByteString' that zeroes its memory during garbage collection, and
-- implements constant-time 'Eq' and 'Ord'.
--
-- It's safe to discard the 'ByeString' wrapper and use the 'ByeString'
-- directly. The memory zeroing is tied to the 'ByteString', not
-- the 'ByeString'.
--
-- Additionally, 'Eq' and 'Ord' are constant time.
newtype ByeString = ByeString B.ByteString
  deriving newtype (Show, GetLength, Peek, IsString)

-- | Constant time.
instance Eq ByeString where
  (==) = constEq
  {-# INLINE (==) #-}

-- | Constant time.
instance Ord ByeString where
  compare = constCompare
  {-# INLINE compare #-}

instance Convert B.ByteString ByeString where
  convert = ByeString
  {-# INLINE convert #-}

instance Convert ByeString B.ByteString where
  convert (ByeString x) = x
  {-# INLINE convert #-}

instance Semigroup ByeString where
  a <> b
    | length a == 0 = b
    | length b == 0 = a
    | otherwise = mconcat [a, b]
  {-# INLINE (<>) #-}

instance Monoid ByeString where
  mempty = ByeString B.empty
  {-# INLINE mempty #-}
  mconcat [] = mempty
  mconcat [x] = x
  mconcat xs = concat xs
  {-# INLINE mconcat #-}

concat :: (Peek a, Alloc b) => [a] -> b
concat as0 =
  let as1 = filter (\a -> length a > 0) as0
      bL = _int $ F.foldl' (+) 0 (fmap (toInteger . length) as1)
   in fst $
        allocFreeze bL $ \outP -> do
          F.foldlM
            (\off a -> peek a $ \aP -> do
               let aL = length a
               BI.memcpy (plusPtr outP off) aP aL
               pure $! off + aL)
            0
            as1

instance Alloc ByeString where
  alloc 0 g = (,) mempty <$> g nullPtr
  alloc len g = do
    fp <- mallocForeignPtrBytes len
    let p = unsafeForeignPtrToPtr fp
    FC.addForeignPtrFinalizer fp $! _memset p len 0x00
    a <- g (castPtr p) `onException` _memset p len 0x00
    touchForeignPtr fp
    pure (ByeString (BI.fromForeignPtr fp 0 len), a)

_memset :: Ptr Word8 -> Int -> Word8 -> IO ()
_memset !p !len !x = case len of
  0 -> pure ()
  _ -> void $ BI.memset p x (fromIntegral len)
{-# INLINE _memset #-}

-- XXX This doesn't really work because most ByteString are PlainPtr inside.
-- addZeroFinalizer :: B.ByteString -> IO ()
-- addZeroFinalizer b = do
--   let (fp, off, len) = BI.toForeignPtr b
--   FC.addForeignPtrFinalizer fp
--     $! zero (plusPtr (unsafeForeignPtrToPtr fp) off) len

--------------------------------------------------------------------------------

toBase16 :: (Peek a, Alloc b) => a -> b
toBase16 bin =
  let binL = length bin
      b16L = _int (toInteger binL * 2)
   in fst $
        allocFreeze b16L $ \b16P -> do
          peek bin $ \binP -> do
            out <- c_by_to_base16 b16P (fromIntegral b16L) binP
            when (out /= 0) $ error "toBase16"

fromBase16 :: (Peek a, Alloc b) => a -> Maybe b
fromBase16 b16 = do
  let b16L :: Int = length b16
  guard (b16L `mod` 2 == 0)
  let binL :: Int = b16L `div` 2
      (bin, ret) = do
        allocFreeze binL $ \binP -> do
          peek b16 $ \b16P -> do
            c_by_from_base16 binP b16P (fromIntegral b16L)
  guard (ret == 0)
  Just bin

fromBase16N :: forall a b. (Peek a, AllocN b) => a -> Maybe b
fromBase16N b16 = do
  let b16L :: Int = length b16
      binL :: Int = fromIntegral (natVal (Proxy @(Length b)))
  guard (binL * 2 == b16L)
  let (bin, ret) = do
        allocFreezeN $ \binP -> do
          peek b16 $ \b16P -> do
            c_by_from_base16 binP b16P (fromIntegral b16L)
  guard (ret == 0)
  Just bin

--------------------------------------------------------------------------------

-- | Construct an 'CSize', or fail if outside bounds.
{-# INLINE _csize #-}
_csize :: Int -> CSize
_csize a
  | a < 0 = error "_csize: too small"
  | otherwise = fromIntegral a

-- | Construct an 'Int', or fail if outside bounds.
{-# INLINE _int #-}
_int :: Integer -> Int
_int a
  | a > toInteger (maxBound :: Int) = error "_int: too large"
  | otherwise = fromIntegral a

-- | Constant-time equality.
{-# INLINE constEq #-}
constEq :: forall a b. (Peek a, Peek b) => a -> b -> Bool
constEq a b = constCompare a b == EQ

-- | Constant-time ordering.
{-# NOINLINE constCompare #-}
constCompare :: forall a b. (Peek a, Peek b) => a -> b -> Ordering
constCompare a b = unsafeDupablePerformIO $ do
  peek a $ \aP -> do
    let aL = _csize (length a)
    peek b $ \bP -> do
      let bL = _csize (length b)
      pure $! compare (c_by_memcmp_const aP aL bP bL) 0

--------------------------------------------------------------------------------

-- | Like the one from the 'constraints' library.
data Dict c where
  Dict :: c => Dict c

--------------------------------------------------------------------------------

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

foreign import ccall unsafe "by.h by_memcmp_const"
  c_by_memcmp_const
    :: Ptr Word8 -- ^ a
    -> CSize -- ^ a_len
    -> Ptr Word8 -- ^ b
    -> CSize -- ^ b_len
    -> CInt

foreign import ccall unsafe "by.h by_store64le"
  c_by_store64le :: Ptr Word8 -> Word64 -> IO ()

foreign import ccall unsafe "by.h by_store64be"
  c_by_store64be :: Ptr Word8 -> Word64 -> IO ()

foreign import ccall unsafe "by.h by_store32le"
  c_by_store32le :: Ptr Word8 -> Word32 -> IO ()

foreign import ccall unsafe "by.h by_store32be"
  c_by_store32be :: Ptr Word8 -> Word32 -> IO ()

foreign import ccall unsafe "by.h by_store16le"
  c_by_store16le :: Ptr Word8 -> Word16 -> IO ()

foreign import ccall unsafe "by.h by_store16be"
  c_by_store16be :: Ptr Word8 -> Word16 -> IO ()

foreign import ccall unsafe "by.h by_load64le"
  c_by_load64le :: Ptr Word8 -> Word64

foreign import ccall unsafe "by.h by_load64be"
  c_by_load64be :: Ptr Word8 -> Word64

foreign import ccall unsafe "by.h by_load32le"
  c_by_load32le :: Ptr Word8 -> Word32

foreign import ccall unsafe "by.h by_load32be"
  c_by_load32be :: Ptr Word8 -> Word32

foreign import ccall unsafe "by.h by_load16le"
  c_by_load16le :: Ptr Word8 -> Word16

foreign import ccall unsafe "by.h by_load16be"
  c_by_load16be :: Ptr Word8 -> Word16

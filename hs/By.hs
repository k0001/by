{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

#include <MachDeps.h>

module By {--}
  ( -- * Length
    GetLength (..)
  , index
  , slice
  , first
  , last
  , null

    -- ** Known
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

    -- * Copy
  , Copy (..)
  , pokeFrom
  , pokeTo
    -- ** Helpers
  , mkPoke
  , mkPokeFromTo

    -- * Read
  , Read (..)
  , unsafeRead

    -- * Write
  , Write
  , write

    -- * Convert
  , Convert (..)

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
  , byteStringToByets

    -- * Base16
  , toBase16
  , toBase16N
  , fromBase16
  , showBase16
  , showsBase16
  , showStringBase16

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
  , HostByteOrder
  , Size
  , Endian(..)
  , encodeLE
  , decodeLE
  , encodeBE
  , decodeBE

  -- * Intervals
  , LengthInterval
  , SliceInterval
  , IndexInterval
  , indexFromSlice
  , sliceFromIndex
  , lengthToSlice
  ) --}
  where

import Control.Exception as Ex
import Control.Monad
import Data.Binary qualified as Bin
import Data.Binary.Get qualified as Bin
import Data.Binary.Put qualified as Bin
import Data.Bits
import Data.ByteString qualified as B
import Data.ByteString.Internal qualified as BI
import Data.Char (chr)
import Data.Coerce
import Data.Constraint
import Data.Constraint.Nat
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Foldable qualified as F
import Data.Int
import Data.IORef
import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Ord
import Data.Proxy
import Data.String
import Data.Tagged
import Data.Type.Ord
import Data.Type.Equality
import Data.Word
import Foreign.C.Types (CInt (..), CSize (..))
import Foreign.Marshal.Alloc qualified as A
import Foreign.Marshal.Utils qualified as A
import Foreign.Ptr (Ptr, nullPtr, plusPtr, castPtr)
import Foreign.Storable (Storable)
import Foreign.Storable qualified as Sto
import GHC.ByteOrder (ByteOrder(..))
import GHC.ForeignPtr
import GHC.TypeLits qualified as GHC
import GHC.TypeNats
import I (I)
import I qualified
import KindInteger qualified as KI
import Memzero qualified
import Prelude hiding (Read, concat, length, replicate, shows, showString, take,
  drop, splitAt, show, read, last, null)
import Prelude qualified
import System.IO.Unsafe (unsafeDupablePerformIO, unsafePerformIO)
import Unsafe.Coerce (unsafeCoerce)


--------------------------------------------------------------------------------

-- | Type suitable for measuring the 'length' of the bytes in @t@.
type LengthInterval (t :: Type) = I CSize (MinLength t) (MaxLength t)

-- | Type suitable for measuring the length of a slice of the bytes in @t@,
-- which may be shorter than 'MinLength'.
type SliceInterval (t :: Type) = I CSize 0 (MaxLength t)

-- | Type suitable for indexing the bytes in @t@.
type IndexInterval (t :: Type) = I CSize 0 (MaxLength t - 1)

-- | Index corresponding to the last byte at the slice of the specified length.
--
-- __NB__: When using this function, many times you will need to
-- specify @t@ using @-XTypeApplications@. Otherwise this won't
-- type-check because neither 'SliceInterval' nor 'IndexInterval'
-- are injective type families.
indexFromSlice
  :: forall t. (GetLength t) => SliceInterval t -> Maybe (IndexInterval t)
{-# NOINLINE indexFromSlice #-} -- so that the Dict stuff happens only once
indexFromSlice = fromMaybe (const Nothing) $ do
  Dict <- leNatural @1 @(MaxLength t)
  Dict <- pure $ evidence (minusNat @(MaxLength t) @1)
  Dict <- leNatural @0 @(MaxLength t - 1)
  Dict <- leNatural @(MaxLength t - 1) @(I.MaxT CSize)
  pure $ \s -> case iToCSize s of
    n | n > 0 -> I.from (n - 1)
    _ -> error "indexFromSlice: impossible?"

-- | Length of the slice through to the byte at the specified index.
--
-- __NB__: When using this function, many times you will need to
-- specify @t@ using @-XTypeApplications@. Otherwise this won't
-- type-check because neither 'IndexInterval' nor 'SliceInterval'
-- are injective type families.
sliceFromIndex
  :: forall t. (GetLength t) => IndexInterval t -> Maybe (SliceInterval t)
sliceFromIndex = withDict (zeroLe @(MaxLength t)) $ \s ->
  case iToCSize s of
    n | n < maxBound -> I.from (n + 1)
    _ -> error "sliceFromIndex: impossible?"

-- | 'I.Up'cast a 'LengthInterval' so that it can be typechecked as a
-- 'SliceInterval'.
--
-- __NB__: When using this function, many times you will need to
-- specify @t@ using @-XTypeApplications@. Otherwise this won't
-- type-check because neither 'LengthInterval' nor 'SliceInterval'
-- are injective type families.
lengthToSlice
  :: forall t. (GetLength t) => LengthInterval t -> SliceInterval t
lengthToSlice = withDict (zeroLe @(MaxLength t)) I.up

-----------------------------------------------------------------------------

-- | Runtime byte length discovery.
class
  ( MaxLength t <= KI.Abs (I.MaxT Int)
  , I.Interval CSize (MinLength t) (MaxLength t)
  , I.Interval CSize 0 (MaxLength t)
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
lengthN = I.known @(Length t)

-- | Length of the slice through to the byte at the specified index,
-- if it is within @t@'s runtime 'length'.
--
-- If @t@ has 'KnownLength', then this is not different from 'sliceFromIndex'.
--
-- For exmple, index @'slice' "hola" 2@ returns @3@,
-- the slice through to the byte at the 2nd index. In this example,
-- indexes 4 and over result in 'Nothing'.
slice
  :: forall t. (GetLength t) => t -> IndexInterval t -> Maybe (SliceInterval t)
slice t i = do s <- sliceFromIndex @t i
               guard (iToInteger s <= iToInteger (length t))
               pure s

-- | Index corresponding to the last byte at the slice of the specified
-- length, if it is within @t@'s runtime 'length'.
--
-- If @t@ has 'KnownLength', then this is not different from 'indexFromSlice'.
--
-- For exmple, @'slice' "hola" 3@ returns @2@, the index of the 3rd byte.
-- In this example, slices 5 and over result in 'Nothing'.
index
  :: forall t. (GetLength t) => t -> SliceInterval t -> Maybe (IndexInterval t)
index t s = do guard (iToInteger s <= iToInteger (length t))
               indexFromSlice @t s

-- | Whether the runtime 'length' of @t@ is @0@.
null :: forall t. (GetLength t) => t -> Bool
null t = iToCSize (length t) == 0

-- | Index to the first byte in @t@, if not 'null'.
--
-- So, this is either 'Nothing' or @'Just' 0@.
first :: forall t. (GetLength t) => t -> Maybe (IndexInterval t)
{-# NOINLINE first #-} -- so that the Dict stuff happens only once
first = fromMaybe (const Nothing) $ do
  Dict <- leNatural @1 @(MaxLength t)
  Dict <- pure $ evidence (minusNat @(MaxLength t) @1)
  Dict <- leNatural @0 @(MaxLength t - 1)
  Dict <- leNatural @(MaxLength t - 1) @(I.MaxT CSize)
  pure $ \t -> do guard (not (By.null t))
                  pure (I.known @0)

-- | Index to the last byte in @t@, if not 'null'.
last :: forall t. (GetLength t) => t -> Maybe (IndexInterval t)
last = indexFromSlice @t . I.up . length

-- | Poke a copy of @t@'s bytes into a user-given address.
class (GetLength t, 1 <= MaxLength t) => Copy t where
  -- | Write a copy of @t@'s bytes into the buffer starting at 'Ptr'.
  --
  -- __WARNING:__
  --
  -- * The caller is responsible for ensuring the the entire 'length' of @t@
  -- will fit in the buffer starting at 'Ptr'.
  --
  -- * The author of this instance must ensure all 'poke' does is write
  -- into the 'Ptr'. Use 'mkPoke' to write a correct implementation.
  -- If there is a 'Read' instance for @t@, 'pokeFromTo' gets a correct default
  -- implementation.
  poke :: t -> Ptr Word8 -> IO ()
  default poke :: Read t => t -> Ptr Word8 -> IO ()
  poke = mkPoke read

  -- | Like 'poke', but instead of writing all the bytes,
  -- @'pokeFromTo' from to t@ only writes the bytes between
  -- @from@ and @to@, inclusive. Returns 'Nothing' if out
  -- @from@ is greater than @to@ or @to@ is greater than
  -- 'last'.
  --
  -- @
  -- 'pokeFromTo' 'I.min' ('last' t) t == 'Just' ('poke' t)
  -- @
  --
  -- __WARNING:__
  --
  -- * The caller is responsible for ensuring the the entire 'length' of @t@
  -- will fit in the buffer starting at 'Ptr'.
  --
  -- * The author of this instance must ensure all 'pokeFromTo' does is write
  -- into the 'Ptr'. Use 'mkPokeFromTo' to write a correct implementation.
  -- If there is a 'Read' instance for @t@, 'pokeFromTo' gets a correct default
  -- implementation.
  pokeFromTo
    :: IndexInterval t -- ^ From (inclusive).
    -> IndexInterval t -- ^ To (inclusive).
    -> t
    -> Maybe (Ptr Word8 -> IO ())
  default pokeFromTo
    :: Read t
    => IndexInterval t
    -> IndexInterval t
    -> t
    -> Maybe (Ptr Word8 -> IO ())
  {-# NOINLINE pokeFromTo #-} -- so that the Dict stuff happens only once
  pokeFromTo = mkPokeFromTo read

-- | You can use @'mkPoke' f@ as definition of the 'poke' method of the
-- 'Copy' instance for your @t@.
--
-- @
-- class (...) => 'Copy' t where
--   'poke' = 'mkPoke' f
--   ...
-- @
mkPoke
  :: forall t
  .  (GetLength t, 1 <= MaxLength t)
  => (t -> (Ptr Word8 -> IO ()) -> IO ())
  -- ^ Like 'read'. Given a @t@ and an 'IO' action that will make a copy of
  -- @'length' t@ bytes starting at the specified 'Ptr', perform that action.
  -> t
  -> Ptr Word8
  -> IO ()
{-# INLINE mkPoke #-}
mkPoke read_ = \s dP ->
  read_ s $ \sP ->
  void $ c_memcpy dP sP (iToCSize (length s))

-- | You can use @'mkPokeFromTo' f@ as definition of the 'pokeFromTo' method
-- of the 'Copy' instance for your @t@.
--
-- @
-- class (...) => 'Copy' t where
--   'pokeFromTo' = 'mkPokeFromTo' f
--   ...
-- @
mkPokeFromTo
  :: forall t
  .  (GetLength t, 1 <= MaxLength t)
  => (t -> (Ptr Word8 -> IO ()) -> IO ())
  -- ^ Like 'read'. Given a @t@ and an 'IO' action that will make a copy of
  -- @'length' t@ bytes starting at the specified 'Ptr', perform that action.
  -> IndexInterval t
  -> IndexInterval t
  -> t
  -> Maybe (Ptr Word8 -> IO ())
{-# INLINE mkPokeFromTo #-}
mkPokeFromTo read_ = g
  where
    {-# NOINLINE g #-}
    g = withDict (minusLe @(MaxLength t) @1 @(MaxLength t))
      $ withDict (leTrans @(MaxLength t - 1) @(MaxLength t) @(KI.Abs (I.MaxT Int)))
      $ \from to s -> do
           guard (iToInt to < iToInt (length s))
           guard (from <= to)
           let len = iToCSize to - iToCSize from + 1
           pure $ \dP -> read_ s $ \sP ->
             void $ c_memcpy dP (plusPtr sP (iToInt from)) len

-- | @
-- 'pokeFrom' from t == 'pokeFromTo' from ('last' t) t
-- @
pokeFrom
  :: forall t
  .  (Copy t)
  => IndexInterval t -- ^ From (inclusive).
  -> t
  -> Maybe (Ptr Word8 -> IO ())
pokeFrom from s = do
  to <- last s
  pokeFromTo from to s

-- | @
-- 'pokeTo' to t == 'pokeFromTo' 'I.min' to t
-- @
pokeTo
  :: forall t
  .  (Copy t)
  => IndexInterval t -- ^ To (inclusive).
  -> t
  -> Maybe (Ptr Word8 -> IO ())
{-# NOINLINE pokeTo #-} -- so that the Dict stuff happens only once
pokeTo to t = do from <- first t
                 pokeFromTo from to t

-- | Raw access to the bytes of @t@ for __read-only__ purposes.
class GetLength t => Read t where
  -- | Access the bytes of @t@ for __read-only__ purposes.
  --
  -- __WARNING__: The caller is responsible for making sure that the passed-in
  -- action is indeed read-only. It must not modify @t@ in any way.
  read :: t
       -> (Ptr Word8 -> IO a)
       -- ^ Read-only interaction with 'length' bytes starting at 'Ptr'.
       -> IO a

-- | Raw access to the bytes of @t@ for __read-write__ purposes.
class Read t => Write t

-- | Access the bytes of @t@ for __read-write__ purposes.
write :: Write t => t -> (Ptr Word8 -> IO a) -> IO a
write = read

-- | Like 'read', but “pure”. This is safe as long as the
-- passed in function only interacts with the 'length' bytes
-- starting at the given 'Ptr' in a **read-only** manner.
unsafeRead
  :: Read t
  => t
  -> (Ptr Word8 -> IO a)
  -- ^ Read-only interaction with 'length' bytes starting at 'Ptr'.
  -> a
unsafeRead t g = unsafeDupablePerformIO (read t g)
{-# NOINLINE unsafeRead #-}

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
replicate :: forall a. Alloc a => LengthInterval a -> Word8 -> a
replicate len x = unsafeAlloc_ len $ \p ->
                  c_memset p x (iToCSize len)

-- | @'replicate' x@ repeats @'Length' a@ times the byte @x@.
replicateN :: forall a. (Alloc a, KnownLength a) => Word8 -> a
replicateN = replicate (lengthN @a)

-- | @'copyN' a@ copies all of @a@ into a newly allocated @b@, if it would fit.
copy :: forall a b. (Copy a, Alloc b) => a -> Maybe b
copy a = do bL <- I.down (length a)
            pure $ unsafeAlloc_ bL (poke a)

-- | @'copyN' a@ copies all of @a@ into a newly allocated @b@.
copyN
  :: forall a b
  .  ( Copy a
     , Alloc b
     , MinLength b <= MinLength a
     , MaxLength a <= MaxLength b )
  => a
  -> b
copyN a = unsafeAlloc_ (I.up (length a)) (poke a)

-- | @'append' a b@ allocates a new @c@ that contains the concatenation of
-- @a@ and @b@, in that order, if it would fit in @c@.
append
  :: forall a b c
  .  ( Copy a
     , Copy b
     , Alloc c )
  => a
  -> b
  -> Maybe c
append a b = do
  aL' <- I.down (length a)
  bL' <- I.down (length b)
  cL  <- I.plus' aL' bL'
  pure $ unsafeAlloc_ cL $ \cP -> do
    poke a cP
    poke b (plusPtr cP (iToInt aL'))

-- | @'append' a b@ allocates a new @c@ that contains the concatenation of
-- @a@ and @b@, in that order.
appendN
  :: forall a b c
  .  ( Copy a
     , Copy b
     , Alloc c
     , MinLength c <= MinLength a + MinLength b
     , MaxLength a + MaxLength b <= MaxLength c )
  => a
  -> b
  -> c
appendN a b = fromMaybe (error "By.appendN: impossible")
                        (append a b)

-- | @'splitAt' n a@ copies the @n@ leading bytes of @a@ into a newly
-- allocated @b@, and the trailing @'length' a - n@ bytes of @a@
-- into a newly allocated @c@, if they would fit.
splitAt
  :: forall a b c
  .  ( Copy a
     , Alloc b
     , Alloc c )
  => SliceInterval a
  -> a
  -> Maybe (b, c)
{-# INLINE splitAt #-}
splitAt bLa a = (,) <$> take bLa a <*> drop bLa a

-- | @'splitAtN' a@ splits @a@ into two parts of known lengths.
--
-- The resulting parts are copies independent from @a@.
splitAtN
  :: forall a b c
  .  ( Copy a
     , Alloc b
     , Alloc c
     , KnownLength a
     , KnownLength b
     , KnownLength c
     , Length a ~ (Length b + Length c) )
  => a
  -> (b, c)
splitAtN a = fromMaybe (error "splitAtN: impossible") $ do
  preSa <- I.down (lengthN @b)
  b <- take preSa a
  c <- drop preSa a
  pure (b, c)

-- | @'take' n a@ copies the @n@ leading bytes of @a@ into a
-- newly allocated @b@, if it would fit.
take
  :: forall a b.
     ( Copy a
     , Alloc b )
  => SliceInterval a
  -> a
  -> Maybe b
take bLsa a = do
  bL :: LengthInterval b <- I.down bLsa
  aTo :: IndexInterval a <- indexFromSlice @a bLsa
  pokeB <- pokeTo aTo a
  pure $ unsafeAlloc_ bL pokeB

-- | @'takeN' a@ copies the leading bytes of @a@ into a
-- newly allocated @b@ of known length.
takeN
  :: forall a b.
     ( Copy a
     , Alloc b
     , KnownLength b
     , Length b <= MinLength a )
  => a
  -> b
takeN = withDict (zeroLe @(MaxLength a)) $ \a ->
        fromMaybe (error "By.takeN: impossible") $ do
           bLa <- I.down (lengthN @b)
           take bLa a

-- | @'drop' n a@ copies the @n@ trailing bytes of @a@ into a newly
-- allocated @b@, if it would fit.
drop
  :: forall a b.
     ( Copy a
     , Alloc b )
  => SliceInterval a
  -> a
  -> Maybe b
{-# NOINLINE drop #-} -- so that the Dict stuff happens only once
drop = fromMaybe (\_ _ -> Nothing) $ do
  Dict <- pure $ evidence (minusNat @(MaxLength a) @1)
  Dict <- pure $ evidence (zeroLe @(MaxLength a - 1))
  Dict <- pure $ evidence (zeroLe @(MaxLength a))
  Dict <- leNatural @(MaxLength a - 1) @(I.MaxT CSize)
  pure $ \preSa a -> do
    -- preSa is 1 past the last index of the prefix,
    -- so it coincides with the first index of the suffix.
    let aL' :: SliceInterval a = lengthToSlice @a (length a)
    bL :: LengthInterval b <- I.down =<< I.minus' aL' preSa
    aFrom :: IndexInterval a <- I.down preSa
    pokeB <- pokeFrom aFrom a
    pure $ unsafeAlloc_ bL pokeB

-- | @'dropN' a@ copies the trailing bytes of @a@ into a
-- newly allocated @b@ of known length.
dropN
  :: forall a b.
     ( Copy a
     , Alloc b
     , KnownLength b
     , Length b <= MinLength a )
  => a
  -> b
dropN = withDict (zeroLe @(MaxLength a)) $ \a ->
  fromMaybe (error "By.dropN: impossible") $ do
    let aL' :: SliceInterval a = lengthToSlice @a (length a)
    bL' :: SliceInterval a <- I.down (lengthN @b)
    preSa :: SliceInterval a <- I.minus' aL' bL'
    drop preSa a

-- | Allocate a new @a@ made up of the bytes in @f@.
-- 'Nothing' if the result wouldn't fit in @a@.
pack :: forall a f. (Alloc a, Foldable f) => f Word8 -> Maybe a
pack ws = do
  aL <- I.from =<< toIntegralSized (F.length ws)
  pure $ unsafeAlloc_ aL $ \aP ->
         F.foldlM (\off w -> do c_memset (plusPtr aP off) w 1
                                pure $! off + 1)
                  0
                  ws

-- | List of bytes in @a@.
unpack :: forall a. Read a => a -> [Word8]
unpack a = unsafeRead a $ f (iToInt (length a))
  where
    f :: Int -> Ptr Word8 -> IO [Word8]
    f 0 !_ = pure []
    f n  p = do !x <- Sto.peek p
                !xs <- f (n - 1) (plusPtr p 1)
                pure (x : xs)

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.show'.
show :: forall a. Read a => a -> String
show = flip shows ""

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.shows'.
shows :: forall a. Read a => a -> ShowS
shows = Prelude.shows . fmap (chr . fromIntegral) . unpack

-- | Renders @a@ as a literal 'String'. This behaves like
-- "Prelude"''s 'Prelude.showString'.
showString :: forall a. Read a => a -> ShowS
showString = Prelude.showString . fmap (chr . fromIntegral) . unpack

-- | Encodes @a@ using base16 encoding and then renders it using 'show'.
--
-- @
-- > 'showBase16' 'True' (\"hello\" :: 'B.ByteString')
-- \"\\"68656C6C6F\\"\"
-- > 'showBase16' 'False' (\"hello\" :: 'B.ByteString')
-- \"\\"68656c6c6f\\"\"
-- @
showBase16
  :: forall a
  .  (Copy a)
  => Bool -- ^ Uppercase if 'True'.
  -> a
  -> String
showBase16 u a = showsBase16 u a ""

-- | Encodes @a@ using Base-16 encoding and then renders it using 'shows'.
--
-- @
-- > 'showsBase16' 'True' (\"hello\" :: 'B.ByteString') \"zzz\"
-- \"\\"68656C6C6F\\"zzz\"
-- > 'showsBase16' 'False' (\"hello\" :: 'B.ByteString') \"zzz\"
-- \"\\"68656c6c6f\\"zzz\"
-- @
showsBase16
  :: forall a
  .  (Copy a)
  => Bool -- ^ Uppercase if 'True'.
  -> a
  -> ShowS
showsBase16 u a = showChar '"' . showStringBase16 u a . showChar '"'

-- | Encodes @a@ using Base-16 encoding and then renders it
-- using 'showString'.
--
-- @
-- > 'showStringBase16' 'True' (\"hello\" :: 'B.ByteString') \"zzz\"
-- \"68656C6C6Fzzz\"
-- > 'showStringBase16' 'False' (\"hello\" :: 'B.ByteString') \"zzz\"
-- \"68656c6c6fzzz\"
-- @
showStringBase16
  :: forall a
  .  (Copy a)
  => Bool -- ^ Uppercase if 'True'.
  -> a
  -> ShowS
showStringBase16 = \u a ->
    -- We use 'Byets' internally because why not.
    case splitAt preLa0 a of
      Just (pre :: Byets, pos :: Byets) ->
        case toBase16 u pre of
          Just (b16 :: Byets) ->
            showString b16 . showStringBase16 u pos
          Nothing -> -- impossible, @pre@ fits in 'Byets'.
            error "showStringBase16: impossible 1"
      Nothing -> -- We copy @a@ to avoid a 'Read' constraint.
        case toBase16 @Byets u =<< copy a of
          Just (b16 :: Byets)-> showString b16
          Nothing -> -- impossible, @a@ fits in 'Byets'.
            error "showStringBase16: impossible 2"
  where
    preLa0 :: SliceInterval a
    preLa0 = withDict (zeroLe @(MaxLength a))
           $ I.clamp (16 * 1024 :: CSize) -- Work in 16KiB chunks

-- | Concatenates all the @a@s. 'Nothing' if the result doesn't fit in @b@.
concat :: forall a b f. (Copy a, Alloc b, Foldable f) => f a -> Maybe b
concat as = do
  -- We add lengths as 'Integer' to avoid overflowing 'Int' while adding.
  bL <- I.from =<< toIntegralSized
            (F.foldl' (\ !z a -> z + iToInteger (length a)) 0 as)
  pure $ unsafeAlloc_ bL $ \outP ->
         F.foldlM (\off a -> do poke a (plusPtr outP off)
                                pure $! off + iToInt (length a))
         0
         as

--------------------------------------------------------------------------------

-- Silly instance just to make sure we don't go making assumptions
-- about 'MinLength'.

-- | Interpreted as 'nullPtr'.
instance GetLength () where
  type MinLength () = 0
  type MaxLength () = 0
  length () = I.known @0

-- | Interpreted as 'nullPtr'.
instance Alloc () where
  alloc _ g = do a <- g nullPtr
                 pure ((), a)

--------------------------------------------------------------------------------

-- | Ad-hoc conversion between types __without copying__ the user data bytes.
class (GetLength a, GetLength b) => Convert a b where
   -- | Convert @a@ to @b@ __without copying__ the user data bytes.
   --
   -- * If the given @a@ fits in @b@, conversion must succeed.
   --
   -- * The 'length' of @a@ and @b@ must be equal.
   --
   -- * The underlying user bytes must be __shared__ by both @a@ and @b@.
   --
   -- * When both are successful, 'convert' and 'convertN' must give the same
   -- result.
  convert :: a -> Maybe b
  default convert
    :: (MinLength b <= MinLength a, MaxLength a <= MaxLength b) => a -> Maybe b
  convert = Just . convertN
  -- | Like 'convert', but always succeeds because @a@ is known to fit in @b@.
  convertN :: (MinLength b <= MinLength a, MaxLength a <= MaxLength b) => a -> b

-- | @
-- 'convert' == 'Just'
-- 'convertN' == 'id'
-- @
instance (GetLength a) => Convert a a where
  convertN = id
  {-# INLINE convertN #-}

instance (KnownLength (Sized len a), KnownLength (Sized len b), Convert a b)
  => Convert (Sized len a) (Sized len b) where
  convertN = \a -> case convert (unSized a) of
    Just b | iToCSize (length a) == iToCSize (length b) -> Sized b
    _ -> error "By.convert(Sized): impossible"

-- | The obtained 'B.ByteString' preserves the memory-zeroing properties.
-- 'convert' always returns 'Just'.
--
-- To convert a 'B.ByteString' to 'Bytes', see 'byteStringToByets'.
instance Convert Byets B.ByteString where
  convertN = \(Byets len fp) -> BI.BS fp (iToInt len)
  {-# INLINE convertN #-}

--------------------------------------------------------------------------------

-- | Convert a 'B.ByteString' to 'Byets' without copying. The original
-- 'B.ByteString' and the 'Bytes' share the underlying bytes, which will be
-- zeroed once both the 'B.ByteString' and the 'Byets' become unreachable.
--
-- This runs on 'IO' because a zeroing finalizer is attached to the original
-- 'B.ByteString'.
byteStringToByets :: B.ByteString -> IO Byets
byteStringToByets t@(BI.BS fp _) = do
  _ <- addForeignPtrFinalizersMemzero (iToCSize (length t)) fp
  pure (Byets (length t) fp)

-- | Adds the "Memzero" wiping finalizer to the 'ForeignPtr'. It will wipe
-- the given 'CSize' number of bytes starting at 'unsafeForeignPtrToPtr'.
--
-- If possible, the C finalizer will be used. Otherwise, the Haskell finalizer
-- will be used.  Returns 'True' if a finalizer was installed, otherwise
-- returns 'False' if the 'ForeignPtr' is a 'PlainPtr' or a 'FinalPtr'.
--
-- __WARNING__: The check to see which kind of finalizer we can add and the
-- actual addition of the finalizer don't happen atommically.
addForeignPtrFinalizersMemzero :: CSize -> ForeignPtr p -> IO Bool
addForeignPtrFinalizersMemzero e fp@(ForeignPtr _ x) = do
  let yiof = case x of
        PlainForeignPtr iof -> Just iof
        MallocPtr _ iof -> Just iof
        PlainPtr _ -> Nothing
        FinalPtr -> Nothing
  case yiof of
    Nothing -> pure False
    Just iof -> do
      readIORef iof >>= \case
        HaskellFinalizers _ ->
          addForeignPtrConcFinalizer fp $
            Memzero.memzero' (unsafeForeignPtrToPtr fp) e
        _ -> Ex.bracketOnError (A.new e) A.free $ \pe ->
          addForeignPtrFinalizerEnv Memzero.finalizerEnvFree pe fp
      pure True

--------------------------------------------------------------------------------

-- | A @t@ whose 'length' is known to be @len@.
newtype Sized (len :: Natural) t = Sized t
  deriving newtype (Show)

deriving newtype instance {-# OVERLAPPABLE #-} Eq t => Eq (Sized len t)
deriving newtype instance {-# OVERLAPPABLE #-} Ord t => Ord (Sized len t)

instance
  ( GetLength (Sized len t)
  , Copy t
  , 1 <= Length (Sized len t)
  ) => Copy (Sized len t) where
  poke (Sized s) dP = poke s dP
  pokeFromTo from to = \(Sized s) ->
    withDict (minusNat @(MaxLength t) @1) $ do
      Dict <- leNatural @0 @(MaxLength t - 1)
      Dict <- leNatural @(MaxLength t - 1) @(I.MaxT CSize)
      -- TODO upcast instead of downcast
      from' <- I.down from
      to' <- I.down to
      pokeFromTo from' to' s

-- TODO: (a <= b) :- ((a - c) <= (b - c))

deriving newtype instance
  ( GetLength (Sized len t)
  , Read t
  ) => Read (Sized len t)

instance
  ( MinLength t <= len
  , len <= MaxLength t
  , len <= KI.Abs (I.MaxT Int)
  , I.Interval CSize len len
  , I.Interval CSize 0 len
  ) => GetLength (Sized len t) where
  type MinLength (Sized len t) = len
  type MaxLength (Sized len t) = len

instance
  ( Alloc t
  , MinLength t <= len
  , len <= MaxLength t
  , KnownLength (Sized len t)
  ) => Alloc (Sized len t) where
  alloc l g = do
    (t, a) <- alloc (I.up l) g
    pure (Sized t, a)

instance KnownLength (Sized len B.ByteString)
  => Bin.Binary (Sized len B.ByteString) where
  put (Sized t) = Bin.putByteString t
  get = fmap Sized $ Bin.getByteString $
          iToInt $ lengthN @(Sized len B.ByteString)

-- | Remove the 'Sized' wraper.
unSized :: Sized len t -> t
unSized = coerce
{-# INLINE unSized #-}

-- | Wrap the @t@ in a 'Sized' if it has the correct length.
sized
  :: forall len t
  .  (KnownNat len, GetLength t)
  => t
  -> Maybe (Sized len t)
sized t = I.with (length t) $ \p -> do
  Refl <- sameNat (Proxy @len) p
  pure (Sized t)

-- | Wrap the @t@ in a 'Sized' if it has the correct length,
-- otherwise fail with 'error'.
unsafeSized
  :: forall len t
  .  (KnownNat len, GetLength t)
  => t
  -> Sized len t
unsafeSized = fromMaybe (error "By.unsafeSized") . sized

-- | Wrap the @t@ in a 'Sized', bringing to scope proofs of its length.
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

-- | Wrap the @t@ in a 'Sized' of some unknown length within @min@ and @max@,
-- | bringing to scope proofs of its length.
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
withSizedMinMax t g = I.with (length t) $ \(Proxy @len) -> do
  Dict <- leNatural @min @len
  Dict <- leNatural @len @max
  withDict (zeroLe @len) $
    withDict (leTrans @len @(MaxLength t) @(KI.Abs (I.MaxT Int))) $
      withDict (leTrans @len @(KI.Abs (I.MaxT Int)) @(I.MaxT CSize)) $
        pure $ g (Sized t :: Sized len t)

-- | Wrap the @t@ in a 'Sized' of length known to be within @min@ and @max@,
-- | bringing to scope proofs of its length.
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
withSizedMinMaxN t f =
  I.with (length t) $ \(_ :: Proxy len) ->
  withDict (zeroLe @len) $
  withDict (leTrans @min @(MinLength t) @len) $
  withDict (leTrans @len @(MaxLength t) @max) $
  withDict (leTrans @len @(MaxLength t) @(KI.Abs (I.MaxT Int))) $
  withDict (leTrans @len @(KI.Abs (I.MaxT Int)) @(I.MaxT CSize)) $
  f (Sized t :: Sized len t)

--------------------------------------------------------------------------------

-- | The size in bytes of a value of type @a@. As in 'Data.Storable.sizeOf'.
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
# error "Unexpected WORD_SIZE_IN_BYTES"
#endif

--------------------------------------------------------------------------------

-- | Conversion between 'HostByteOrder' and 'LittleEndian' or
-- 'BigEndian' byte order.
class Endian a where
  {-# MINIMAL hToLE, hToBE, leToH, beToH #-}
  -- | From 'HostByteOrder' to 'LittleEndian' byte order.
  hToLE :: a -> Tagged 'LittleEndian a
  -- | From 'HostByteOrder' to 'BigEndian' byte order.
  hToBE :: a -> Tagged 'BigEndian a
  -- | From 'LittleEndian' byte order to 'HostByteOrder'.
  leToH :: Tagged 'LittleEndian a -> a
  -- | From 'BigEndian' byte order to 'HostByteOrder'.
  beToH :: Tagged 'BigEndian a -> a

  -- | Write @a@ into the 'Ptr' as @'Size' a@ bytes in 'LittleEndian' byte order.
  -- The input @a@ is in 'HostByteOrder'.
  pokeLE :: Ptr (Tagged 'LittleEndian a) -> a -> IO ()
  default pokeLE :: Storable a => Ptr (Tagged 'LittleEndian a) -> a -> IO ()
  pokeLE p = Sto.poke p . hToLE
  {-# INLINE pokeLE #-}

  -- | Read @a@ from the 'Ptr' containing @'Size' a@ bytes in 'LittleEndian' byte order.
  -- The output @a@ is in 'HostByteOrder'.
  peekLE :: Ptr (Tagged 'LittleEndian a) -> IO a
  default peekLE :: Storable a => Ptr (Tagged 'LittleEndian a) -> IO a
  peekLE = fmap leToH . Sto.peek
  {-# INLINE peekLE #-}

  -- | Write @a@ into the 'Ptr' as @'Size' a@ bytes in 'BigEndian' byte order.
  -- The input @a@ is in 'HostByteOrder'.
  pokeBE :: Ptr (Tagged 'BigEndian a) -> a -> IO ()
  default pokeBE :: Storable a => Ptr (Tagged 'BigEndian a) -> a -> IO ()
  pokeBE p = Sto.poke p . hToBE
  {-# INLINE pokeBE #-}

  -- | Read @a@ from the 'Ptr' containing @'Size' a@ bytes in 'BigEndian' byte order.
  -- The output @a@ is in 'HostByteOrder'.
  peekBE :: Ptr (Tagged 'BigEndian a) -> IO a
  default peekBE :: Storable a => Ptr (Tagged 'BigEndian a) -> IO a
  peekBE = fmap beToH . Sto.peek
  {-# INLINE peekBE #-}

-- | Encodes @a@ as @leNatural@ using 'LittleEndian' byte order.
-- The input @a@ is in 'HostByteOrder'.
encodeLE
  :: forall a le
  .  ( Endian a, Alloc le, KnownNat (Size a)
     , MinLength le <= Size a, Size a <= MaxLength le )
  => a -> le
encodeLE = \a -> unsafeAlloc_ (I.known @(Size a)) $ \p ->
                 pokeLE (castPtr p) a

-- | Writes @a@ in @be@ using 'BigEndian' byte order.
-- The input @a@ is in 'HostByteOrder'.
encodeBE
  :: forall a be
  .  ( Endian a, Alloc be, KnownNat (Size a)
     , MinLength be <= Size a, Size a <= MaxLength be )
  => a -> be
encodeBE = \a -> unsafeAlloc_ (I.known @(Size a)) $ \p ->
                 pokeBE (castPtr p) a

-- | Reads @a@ from @le@ using 'LittleEndian' byte order.
-- The output @a@ is in 'HostByteOrder'.
decodeLE :: forall le a. (Endian a, Read le, Size a ~ Length le) => le -> a
decodeLE le = unsafeRead le (peekLE . castPtr)

-- | Reads @a@ from @be@ using 'BigEndian' byte order.
-- The output @a@ is in 'HostByteOrder'.
decodeBE :: forall be a. (Endian a, Read be, Size a ~ Length be) => be -> a
decodeBE le = unsafeRead le (peekBE . castPtr)

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
  leToH = fromIntegral @Word . leToH . fromIntegral . unTagged
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
  leToH = fromIntegral @Word . leToH . fromIntegral . unTagged
  beToH = fromIntegral @Word . beToH . fromIntegral . unTagged

instance Endian Word where
#if WORD_SIZE_IN_BITS == 64
  hToLE = fmap (fromIntegral @Word64) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word64) . hToBE . fromIntegral
  leToH = fromIntegral @Word64 . leToH . fromIntegral . unTagged
  beToH = fromIntegral @Word64 . beToH . fromIntegral . unTagged
#elif WORD_SIZE_IN_BITS == 32
  hToLE = fmap (fromIntegral @Word32) . hToLE . fromIntegral
  hToBE = fmap (fromIntegral @Word32) . hToBE . fromIntegral
  leToH = fromIntegral @Word32 . leToH . fromIntegral . unTagged
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
type HostByteOrder = 'BigEndian :: ByteOrder
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
type HostByteOrder = 'LittleEndian :: ByteOrder
#endif


--------------------------------------------------------------------------------

-- | @'padLeftN' w a@ extends @a@ with zero or more @w@s on its left.
-- Returns a copy.
padLeftN
  :: forall a b
  .  ( Copy a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padLeftN w a = do
  let dLi = iToInt (lengthN @b) - iToInt (length a) -- positive: len a <= len b
  unsafeAllocN_ $ \bP -> do
    c_memset bP w (fromIntegral dLi)
    poke a (plusPtr bP dLi)

-- | @'padRightN' w a@ extends @a@ with zero or more @w@s on its right.
-- Returns a copy.
padRightN
  :: forall a b
  .  ( Copy a
     , Alloc b
     , KnownLength b
     , MaxLength a <= Length b )
  => Word8
  -> a
  -> b
padRightN w a = do
  let aL = length a
      dLi = iToInt (lengthN @b) - iToInt aL -- positive: aL <= len b
  unsafeAllocN_ $ \bP -> do
    poke a bP
    c_memset (plusPtr bP (iToInt aL)) w (fromIntegral dLi)

--------------------------------------------------------------------------------

instance GetLength B.ByteString where
  type MinLength B.ByteString = 0
  type MaxLength B.ByteString = KI.Abs (I.MaxT Int)
  length x = fromMaybe (error "By.lenght: unexpected ByteString length") $
               I.from =<< toIntegralSized (B.length x)


instance Copy B.ByteString

instance Read B.ByteString where
  read bs g = do
    let (fp, off, _len) = BI.toForeignPtr bs
    withForeignPtr fp $ \p -> g $! plusPtr p off

instance Alloc B.ByteString where
  alloc len g = do
    let len' = iToInt len
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
-- add up to more than @'I.MaxBound' 'Int'@, this 'error's. Notice that this is
-- true of types like 'B.ByteString', too. Use 'concat' if you are
-- paranoid.
instance Semigroup Byets where
  a <> b | iToCSize (length a) == 0 = b
         | iToCSize (length b) == 0 = a
         | otherwise = fromMaybe (error "By.Byets.(<>): too long") (append a b)

-- | See the 'Semigroup' instance for 'Byets'.
instance Monoid Byets where
  {-# NOINLINE mempty #-}
  mempty = unsafePerformIO $ do
    fp <- newForeignPtr_ nullPtr
    pure $ Byets (I.known @0) fp
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
    let aL = iToCSize (length a)
        bL = iToCSize (length b)
    read a $ \pa -> read b $ \pb ->
      pure $ if aL == bL
        then c_by_memeql_ct pa pb aL
        else 0 == c_memcmp pa pb aL

-- | __Constant time__ when the 'Byets' have the same 'length'.
-- Variable time otherwise.
instance Ord Byets where
  {-# NOINLINE compare #-}
  compare a b = unsafeDupablePerformIO $ do
    let aL = iToCSize (length a)
        bL = iToCSize (length b)
    read a $ \pa -> read b $ \pb ->
      pure $ if aL == bL
        then compare (c_by_memcmp_be_ct pa pb aL) 0
        else case c_memcmp pa pb aL of
               0 -> compare aL bL
               x -> compare x 0


-- | __Constant time__. A bit more efficient than the default instance.
instance {-# OVERLAPS #-} Read (Sized len Byets)
  => Eq (Sized len Byets) where
  a == b = unsafeDupablePerformIO $
    read a $ \pa ->
    read b $ \pb ->
    pure $ c_by_memeql_ct pa pb (iToCSize (length a))

-- | __Constant time__. A bit more efficient than the default instance.
instance {-# OVERLAPS #-} Read (Sized len Byets)
  => Ord (Sized len Byets) where
  {-# NOINLINE compare #-}
  compare a b = unsafeDupablePerformIO $
    read a $ \pa ->
    read b $ \pb ->
    pure $ compare (c_by_memcmp_be_ct pa pb (iToCSize (length a))) 0

instance GetLength Byets where
  type MinLength Byets = 0
  type MaxLength Byets = KI.Abs (I.MaxT Int)
  length (Byets len _) = len

instance Copy Byets

instance Read Byets where
  read (Byets _ fp) g = withForeignPtr fp g

-- | The allocated bytes will be automatically zeroed once they become
-- unreachable.
instance Alloc Byets where
  alloc len g = do
    fp <- Memzero.mallocForeignPtrBytes (iToInt len)
    a <- withForeignPtr fp g
    pure (Byets len fp, a)

--------------------------------------------------------------------------------

-- | Encode @a@ as base-16. 'Nothing' if result doesn't fit in @b@.
toBase16 :: (Read a, Alloc b)
         => Bool -- ^ Uppercase if 'True'.
         -> a
         -> Maybe b
toBase16 u = \bin -> do
    b16L <- I.from =<< toIntegralSized (2 * iToInteger (length bin))
    pure $ unsafeAlloc_ b16L $ \b16P ->
           read bin $ \binP ->
           f b16P binP (iToCSize (length bin))
  where
    f = if u then c_by_to_base16_upper
             else c_by_to_base16_lower

-- | Encode @a@ as base-16. The result is known to fit in @b@.
toBase16N
 :: forall a b
 .  ( Read a
    , Alloc b
    , MinLength b <= MinLength a * 2
    , MaxLength a * 2 <= MaxLength b )
 => Bool -- ^ Uppercase if 'True'.
 -> a
 -> b
toBase16N u = fromMaybe (error "By.toBase16N: impossible") . toBase16 u

-- | Decode base16-encoded bytes.
--
-- Succeeds on /even/ number of /lowercase/ base16 input bytes:
--
-- @
-- > 'fromBase16' (\"68656c6c6f\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Just' \"hello\"
-- @
--
-- Succeeds on /even/ number of /upercase/ base16 input bytes:
--
-- @
-- > 'fromBase16' (\"68656C6C6F\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Just' \"hello\"
-- @
--
-- Succeeds on /even/ number of /mixed case/ base16 input bytes:
--
-- @
-- > 'fromBase16' (\"68656c6c6F\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Just' \"hello\"
-- @
--
-- Succeeds on empty input bytes:
--
-- @
-- > 'fromBase16' (\"\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Just' \"\"
-- @
--
-- Fails on /odd/ number of input bytes:
--
-- @
-- > 'fromBase16' (\"48ac1\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Nothing'
-- @
--
-- Fails on non-base16-encoded input bytes:
--
-- @
-- > 'fromBase16' (\"hello\" :: 'B.ByteString') :: 'Maybe' 'B.ByteString'
-- 'Nothing'
-- @
fromBase16 :: forall a b. (Read a, Alloc b) => a -> Maybe b
fromBase16 b16 = do
  let b16L = length b16
  binL <- case divMod (iToCSize b16L) 2 of
            (d, 0) -> I.from d
            _      -> Nothing
  let (bin, ret) = unsafeAlloc binL $ \binP ->
                   read b16 $ \b16P ->
                   c_by_from_base16 binP (iToCSize binL) b16P
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

--------------------------------------------------------------------------

iToCSize :: forall l r. I CSize l r -> CSize
iToCSize = I.unwrap

iToInt :: forall l r. (r <= KI.Abs (I.MaxT Int)) => I CSize l r -> Int
iToInt = fromIntegral . iToCSize

iToInteger :: forall l r. I CSize l r -> Int
iToInteger = fromIntegral . iToCSize

--------------------------------------------------------------------------------

leNatural :: forall l r. (KnownNat l, KnownNat r) => Maybe (Dict (l <= r))
leNatural = case cmpNat (Proxy @l) (Proxy @r) of
  EQI -> Just $ unsafeCoerce (Dict @())
  LTI -> Just $ unsafeCoerce (Dict @())
  GTI -> Nothing

minusLe :: forall (a :: Nat) (b :: Nat) (c :: Nat)
        .  (a <= c, b <= c, b <= a) :- ((a - b) <= c)
minusLe = unsafeCoerceConstraint


{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables#-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

#include <MachDeps.h>

module Interval {--}
 ( -- * Interval
   Interval
 , TypeInterval
 , interval
 , interval'
 , intervalVal
 , intervalFrom
 , intervalFrom'
 , unInterval
 , unInterval'
 , fromInterval
 , KnownInterval
 , KnownTypeInterval
 , IntervalEnds
 , IntervalType

 , MinInterval(..)
 , MaxInterval(..)

 -- * Casting
 , Upcast(..)
 , upcastIntegral
 , upcastReal
 , upcastRealFloat
 , upcastEnd
 , upcast'

 , Downcast(..)
 , downcastIntegral
 , downcastReal
 , downcastRealFloat
 , downcastEnd
 , downcast'

 -- * Endpoints
 , End(..)
 , Ends(..)
 , EndsL
 , EndsR
 , KnownEnd(..)
 , KnownEnds
 , endsVal
 , TypeEnds
 , Contains
 , contains
 , proveContains
 , SubOf
 , transSub
 , supContains
 , Ordered
   -- ** 'Ends' constructors
 , type CC
 , type CO
 , type CCu
 , type COu
 , type OC
 , type OO
 , type OCu
 , type OOu
 , type CuC
 , type CuO
 , type CuCu
 , type CuOu
 , type OuC
 , type OuO
 , type OuCu
 , type OuOu

 -- * Bounds
 , MinBound
 , MinBoundKind
 , MaxBound
 , MaxBoundKind

 -- * Infinity
 , GetNegInfinity
 , HasNegInfinity(..)
 , GetPosInfinity
 , HasPosInfinity(..)

 -- * Utils
 , KnownNum(..)
 , Succ
 , Pred
 , type (<)
 , type (<=)
 , type (>=)
 , type (>)
 , type (<?)
 , type (<=?)
 , type (>=?)
 , type (>?)
 ) --}
 where

import Control.Monad ((<=<), guard)
import Data.Coerce (coerce)
import Data.Constraint
import Data.Int
import Data.Kind
import Data.Proxy
import Data.Ratio (Ratio)
import Data.Type.Bool
import Data.TypeLits hiding (type (<=), type (<), type (>), type (>=))
import Data.Word
import Foreign.C.Types (CSize)
import Numeric.Natural
import Text.Read (readPrec)
import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

class Contains (TypeEnds a) t => KnownNum (t :: k) (a :: Type) where
  numVal :: Proxy t -> a

instance
  ( Num a
  , KnownNat n
  , Contains (TypeEnds a) n
  ) => KnownNum (n :: Nat) a where
  numVal = fromIntegral . natVal
  {-# INLINE numVal #-}

instance
  ( Num a
  , KnownInt i
  , Contains (TypeEnds a) i
  ) => KnownNum (i :: TInt) a where
  numVal = fromIntegral . intVal
  {-# INLINE numVal #-}

instance {-# OVERLAPPABLE #-}
  ( KnownRatInfinity (n ':% 0) a
  , Contains (TypeEnds a) (n ':% 0)
  ) => KnownNum ((n ':% 0) :: Rat) a where
  numVal = ratInfinityVal
  {-# INLINE numVal #-}

instance {-# OVERLAPPABLE #-}
  ( KnownNumRatSimplified (Simplify r) a
  , Contains (TypeEnds a) r
  ) => KnownNum (r :: Rat) a where
  numVal (_ :: Proxy r) = numValRatSimplified (Proxy @(Simplify r))
  {-# INLINE numVal #-}

class KnownNumRatSimplified (r :: Rat) (a :: Type) where
  numValRatSimplified :: Proxy r -> a

instance KnownNum t a => KnownNumRatSimplified (t ':% 1) a where
  numValRatSimplified (_ :: Proxy (t ':% 1)) = numVal (Proxy @t)
  {-# INLINE numValRatSimplified #-}

instance {-# OVERLAPPABLE #-}
  ( Fractional a
  , KnownRat r
  , Contains (TypeEnds a) r
  ) => KnownNumRatSimplified r a where
  numValRatSimplified = fromRational . ratVal
  {-# INLINE numValRatSimplified #-}

class Denominator r ~ 0 => KnownRatInfinity (r :: Rat) (a :: Type) where
  ratInfinityVal :: Proxy r -> a
  ratInfinityVal = error "ratInfinityVal"

instance TypeError ('Text "0/0 is not defined")
  => KnownRatInfinity (0 ':% 0) a where
instance TypeError ('Text "0/0 is not defined ")
  => KnownRatInfinity ('Pos 0 ':% 0) a
instance TypeError ('Text "0/0 is not defined")
  => KnownRatInfinity ('Neg 0 ':% 0) a
instance {-# OVERLAPPABLE #-}
  HasPosInfinity a => KnownRatInfinity ((n :: Nat) ':% 0) a where
  ratInfinityVal _ = posInfinity
instance {-# OVERLAPPABLE #-}
  HasPosInfinity a => KnownRatInfinity (('Pos n :: TInt) ':% 0) a where
  ratInfinityVal _ = posInfinity
instance {-# OVERLAPPABLE #-}
  HasNegInfinity a => KnownRatInfinity (('Neg n :: TInt) ':% 0) a where
  ratInfinityVal _ = negInfinity

--------------------------------------------------------------------------------

-- | Implement instances of 'HasNegInfinity' for types that support negative
-- infinity. Also, implement a 'GetNegInfinity' instance.
class HasNegInfinity (a :: Type) where
  negInfinity :: a

-- | Implement instances of 'GetNegInfinity' for types that support negative
-- infinity. Also, implement a 'HasNegInfinity' instance.
class GetNegInfinity (a :: Type) where
  -- | Negative infinity value, if any.
  getNegInfinityDict :: Maybe (Dict (HasNegInfinity a))
  default getNegInfinityDict
    :: HasNegInfinity a => Maybe (Dict (HasNegInfinity a))
  getNegInfinityDict = Just Dict

-- | Fallback instance. No infinity.
instance {-# OVERLAPPABLE #-} GetNegInfinity a where
  getNegInfinityDict = Nothing

ifNegInfinity
  :: forall a b
  .  GetNegInfinity a
  => (HasNegInfinity a => b)
  -> b
  -> b
ifNegInfinity = case getNegInfinityDict @a of
  Nothing   -> \_ b -> b
  Just Dict -> \b _ -> b

--------------------------------------------------------------------------------

-- | Implement instances of 'HasPosInfinity' for types that support positive
-- infinity. Also, implement a 'GetPosInfinity' instance.
class HasPosInfinity (a :: Type) where
  posInfinity :: a

-- | Implement instances of 'GetPosInfinity' for types that support positive
-- infinity. Also, implement a 'HasPosInfinity' instance.
class GetPosInfinity (a :: Type) where
  -- | Posative infinity value, if any.
  getPosInfinityDict :: Maybe (Dict (HasPosInfinity a))
  default getPosInfinityDict
    :: HasPosInfinity a => Maybe (Dict (HasPosInfinity a))
  getPosInfinityDict = Just Dict

-- -- | Fallback instance. No infinity.
instance {-# OVERLAPPABLE #-} GetPosInfinity a where
  getPosInfinityDict = Nothing

ifPosInfinity
  :: forall a b
  .  GetPosInfinity a
  => (HasPosInfinity a => b)
  -> b
  -> b
ifPosInfinity = case getPosInfinityDict @a of
  Nothing   -> \_ b -> b
  Just Dict -> \b _ -> b

--------------------------------------------------------------------------------

-- | Left and right interval endpoints.
--
-- At the type-level, it may be more comfortable to use 'CC', 'CO', 'CCu' and
-- friends to construct types of this kind.
data Ends l r = Ends
  { endsL :: End l -- ^ Left interval endpoint. Term-level version of 'EndsL'.
  , endsR :: End r -- ^ Right interval endpoint. Term-level version of 'EndsR'.
  }

-- | Left interval endpoint. Type-level version of 'endsL'.
type family EndsL (e :: Ends l r) :: End l where EndsL ('Ends l _) = l
-- | Right interval endpoint. Type-level version of 'endsR'.
type family EndsR (e :: Ends l r) :: End r where EndsR ('Ends _ r) = r

-- | @[l, r]@
type CC   l r = 'Ends ('C l) ('C r)
-- | @[l, r)@
type CO   l r = 'Ends ('C l) ('O r)
-- | @[l, ∞]@
type CCu  l   = 'Ends ('C l) 'Cu
-- | @[l, ∞)@
type COu  l   = 'Ends ('C l) 'Ou
-- | @(l, r]@
type OC   l r = 'Ends ('O l) ('C r)
-- | @(l, r)@
type OO   l r = 'Ends ('O l) ('O r)
-- | @(l, ∞]@
type OCu  l   = 'Ends ('O l) 'Cu
-- | @(l, ∞)@
type OOu  l   = 'Ends ('O l) 'Ou
-- | @[-∞, r]@
type CuC  r   = 'Ends 'Cu    ('C r)
-- | @[-∞, r)@
type CuO  r   = 'Ends 'Cu    ('O r)
-- | @[-∞, ∞]@
type CuCu     = 'Ends 'Cu    'Cu
-- | @[-∞, ∞)@
type CuOu     = 'Ends 'Cu    'Ou
-- | @(-∞, r]@
type OuC  r   = 'Ends 'Ou    ('C r)
-- | @(-∞, r)@
type OuO  r   = 'Ends 'Ou    ('O r)
-- | @(-∞, ∞]@
type OuCu     = 'Ends 'Ou    'Cu
-- | @(-∞, ∞)@
type OuOu     = 'Ends 'Ou    'Ou

--------------------------------------------------------------------------------

data End x
  = C x -- ^ __C__losed.
  | Cu  -- ^ __C__losed __u__nbounded.
  | O x -- ^ __O__pen.
  | Ou  -- ^ __O__pen __u__nbounded.

--------------------------------------------------------------------------------

class KnownEnd (e :: End x) (a :: Type) where
  endVal :: Proxy e -> End a

instance KnownEnd 'Ou a where
  endVal _ = Ou
  {-# INLINE endVal #-}
instance KnownEnd 'Cu a where
  endVal _ = Cu
  {-# INLINE endVal #-}
instance KnownNum x a => KnownEnd ('C x) a where
  endVal (_ :: Proxy ('C x)) = C (numVal (Proxy @x))
  {-# INLINE endVal #-}
instance KnownNum x a => KnownEnd ('O x) a where
  endVal (_ :: Proxy ('O x)) = O (numVal (Proxy @x))
  {-# INLINE endVal #-}

--------------------------------------------------------------------------------

endsVal :: KnownEnds e a => Proxy e -> Ends a a
endsVal (_ :: Proxy e) = Ends (endVal (Proxy @(EndsL e)))
                              (endVal (Proxy @(EndsR e)))
{-# INLINE endsVal #-}

type KnownEnds (e :: Ends l r) (a :: Type)
  = (KnownEnd (EndsL e) a, KnownEnd (EndsR e) a)
       :: Constraint

--------------------------------------------------------------------------------


-- | @sub `'SubOf'` sup@ is satisfied if the interval ends 'sub' are a interval
-- of @sup@.
class (sub :: Ends lsub rsub) `SubOf` (sup :: Ends lsup rsup) where

instance (a <= m, m <= n, n <= z) => CC m n `SubOf` CC a z
instance (a <= m, m <= n, n <= z) => CO m n `SubOf` CC a z
instance (a <= m, m <= n, n <= z) => OC m n `SubOf` CC a z
instance (a <= m, m <= n, n <= z) => OO m n `SubOf` CC a z

instance (a <= m, m <= n        ) => CC m n `SubOf` CCu a
instance (a <= m, m <= n        ) => CO m n `SubOf` CCu a
instance (a <= m                ) => CCu m  `SubOf` CCu a
instance (a <= m                ) => COu m  `SubOf` CCu a
instance (a <= m, m <= n        ) => OC m n `SubOf` CCu a
instance (a <= m, m <= n        ) => OO m n `SubOf` CCu a
instance (a <= m                ) => OCu m  `SubOf` CCu a
instance (a <= m                ) => OOu m  `SubOf` CCu a

instance (a <= m, m <= n, n <  z) => CC m n `SubOf` CO a z
instance (a <= m, m <= n, n <= z) => CO m n `SubOf` CO a z
instance (a <= m, m <= n, n <  z) => OC m n `SubOf` CO a z
instance (a <= m, m <= n, n <= z) => OO m n `SubOf` CO a z

instance (a <= m, m <= n        ) => CC m n `SubOf` COu a
instance (a <= m, m <= n        ) => CO m n `SubOf` COu a
instance (a <= m                ) => COu m  `SubOf` COu a
instance (a <= m, m <= n        ) => OC m n `SubOf` COu a
instance (a <= m, m <= n        ) => OO m n `SubOf` COu a
instance (a <= m                ) => OOu m  `SubOf` COu a

instance (        m <= n, n <= z) => CC m n `SubOf` CuC z
instance (        m <= n, n <= z) => CO m n `SubOf` CuC z
instance (                n <= z) => CuC n  `SubOf` CuC z
instance (                n <= z) => CuO n  `SubOf` CuC z
instance (        m <= n, n <= z) => OC m n `SubOf` CuC z
instance (        m <= n, n <= z) => OO m n `SubOf` CuC z
instance (                n <= z) => OuC n  `SubOf` CuC z
instance (                n <= z) => OuO n  `SubOf` CuC z

instance (                      ) => CC m n `SubOf` CuCu
instance (                      ) => CO m n `SubOf` CuCu
instance (                      ) => CCu m  `SubOf` CuCu
instance (                      ) => COu m  `SubOf` CuCu
instance (                      ) => CuC m  `SubOf` CuCu
instance (                      ) => CuO m  `SubOf` CuCu
instance (                      ) => CuCu   `SubOf` CuCu
instance (                      ) => CuOu   `SubOf` CuCu
instance (                      ) => OC m n `SubOf` CuCu
instance (                      ) => OO m n `SubOf` CuCu
instance (                      ) => OCu m  `SubOf` CuCu
instance (                      ) => OOu m  `SubOf` CuCu
instance (                      ) => OuC n  `SubOf` CuCu
instance (                      ) => OuO n  `SubOf` CuCu
instance (                      ) => OuCu   `SubOf` CuCu
instance (                      ) => OuOu   `SubOf` CuCu

instance (        m <= n, n <  z) => CC m n `SubOf` CuO z
instance (        m <= n, n <= z) => CO m n `SubOf` CuO z
instance (                n <= z) => CuC n  `SubOf` CuO z
instance (                n <  z) => CuO n  `SubOf` CuO z
instance (        m <= n, n <= z) => OC m n `SubOf` CuO z
instance (        m <= n, n <  z) => OO m n `SubOf` CuO z
instance (                n <= z) => OuC n  `SubOf` CuO z
instance (                n <  z) => OuO n  `SubOf` CuO z

instance (                      ) => CC m n `SubOf` CuOu
instance (                      ) => CO m n `SubOf` CuOu
instance (                      ) => COu m  `SubOf` CuOu
instance (                      ) => CuC m  `SubOf` CuOu
instance (                      ) => CuO m  `SubOf` CuOu
instance (                      ) => CuOu   `SubOf` CuOu
instance (                      ) => OC m n `SubOf` CuOu
instance (                      ) => OO m n `SubOf` CuOu
instance (                      ) => OOu m  `SubOf` CuOu
instance (                      ) => OuC m  `SubOf` CuOu
instance (                      ) => OuO n  `SubOf` CuOu
instance (                      ) => OuOu   `SubOf` CuOu

instance (a <  m, m <= n, n <= z) => CC m n `SubOf` OC a z
instance (a <  m, m <= n, n <= z) => CO m n `SubOf` OC a z
instance (a <= m, m <= n, n <= z) => OC m n `SubOf` OC a z
instance (a <= m, m <= n, n <= z) => OO m n `SubOf` OC a z

instance (a <  m, m <= n        ) => CC m n `SubOf` OCu a
instance (a <  m, m <= n        ) => CO m n `SubOf` OCu a
instance (a <  m                ) => CCu m  `SubOf` OCu a
instance (a <  m                ) => COu m  `SubOf` OCu a
instance (a <= m, m <= n        ) => OC m n `SubOf` OCu a
instance (a <= m, m <= n        ) => OO m n `SubOf` OCu a
instance (a <= m                ) => OCu m  `SubOf` OCu a
instance (a <= m                ) => OOu m  `SubOf` OCu a

instance (a <  m, m <= n, n <  z) => CC m n `SubOf` OO a z
instance (a <  m, m <= n, n <= z) => CO m n `SubOf` OO a z
instance (a <= m, m <= n, n <  z) => OC m n `SubOf` OO a z
instance (a <= m, m <= n, n <= z) => OO m n `SubOf` OO a z

instance (a <  m, m <= n        ) => CC m n `SubOf` OOu a
instance (a <  m, m <= n        ) => CO m n `SubOf` OOu a
instance (a <  m                ) => COu m  `SubOf` OOu a
instance (a <= m, m <= n        ) => OC m n `SubOf` OOu a
instance (a <= m, m <= n        ) => OO m n `SubOf` OOu a
instance (a <= m                ) => OOu m  `SubOf` OOu a

instance (        m <= n, n <= z) => CC m n `SubOf` OuC z
instance (        m <= n, n <= z) => CO m n `SubOf` OuC z
instance (        m <= n, n <= z) => OC m n `SubOf` OuC z
instance (        m <= n, n <= z) => OO m n `SubOf` OuC z
instance (                n <= z) => OuC n  `SubOf` OuC z
instance (                n <= z) => OuO n  `SubOf` OuC z

instance (                      ) => CC m n `SubOf` OuCu
instance (                      ) => CCu m  `SubOf` OuCu
instance (                      ) => CO m n `SubOf` OuCu
instance (                      ) => COu m  `SubOf` OuCu
instance (                      ) => OC m n `SubOf` OuCu
instance (                      ) => OCu m  `SubOf` OuCu
instance (                      ) => OO m n `SubOf` OuCu
instance (                      ) => OOu m  `SubOf` OuCu
instance (                      ) => OuC n  `SubOf` OuCu
instance (                      ) => OuCu   `SubOf` OuCu
instance (                      ) => OuO n  `SubOf` OuCu
instance (                      ) => OuOu   `SubOf` OuCu

instance (        m <= n, n <  z) => CC m n `SubOf` OuO z
instance (        m <= n, n <= z) => CO m n `SubOf` OuO z
instance (        m <= n, n <  z) => OC m n `SubOf` OuO z
instance (        m <= n, n <= z) => OO m n `SubOf` OuO z
instance (                n <  z) => OuC n  `SubOf` OuO z
instance (                n <= z) => OuO n  `SubOf` OuO z

instance (                      ) => CC m n `SubOf` OuOu
instance (                      ) => CO m n `SubOf` OuOu
instance (                      ) => COu m  `SubOf` OuOu
instance (                      ) => OC m n `SubOf` OuOu
instance (                      ) => OO m n `SubOf` OuOu
instance (                      ) => OOu m  `SubOf` OuOu
instance (                      ) => OuC n  `SubOf` OuOu
instance (                      ) => OuO n  `SubOf` OuOu
instance (                      ) => OuOu   `SubOf` OuOu

--------------------------------------------------------------------------------


-- | @'Contains' ends a@ is satisfied if @ends@ contains @a@.
class (ContainsL (EndsL e) x, ContainsR (EndsR e) x) => Contains (e :: Ends l r) (x :: k)
instance (ContainsL (EndsL e) x, ContainsR (EndsR e) x) => Contains (e :: Ends l r) (x :: k)

class ContainsL (e :: End r) (x :: k)
instance ContainsL 'Cu x
instance (0 < Denominator x) => ContainsL 'Ou (x :: Rat)
instance ContainsL 'Ou (x :: Nat)
instance ContainsL 'Ou (x :: TInt)
instance (l <= x) => ContainsL ('C l) x
instance (l < x) => ContainsL ('O l) x

class ContainsR (e :: End r) (x :: k)
instance ContainsR 'Cu x
instance (0 < Denominator x) => ContainsR 'Ou (x :: Rat)
instance ContainsR 'Ou (x :: Nat)
instance ContainsR 'Ou (x :: TInt)
instance (x <= r) => ContainsR ('C r) x
instance (x < r) => ContainsR ('O r) x

type EndsErrorMessage :: Ends l r -> ErrorMessage
type family EndsErrorMessage e where
  EndsErrorMessage (CC l r) = 'Text "[" ':<>: 'ShowType l ':<>: 'Text ", " ':<>: 'ShowType r ':<>: 'Text "]"
  EndsErrorMessage (CCu l) = 'Text "[" ':<>: 'ShowType l ':<>: 'Text ", +infinity]"
  EndsErrorMessage (COu l) = 'Text "[" ':<>: 'ShowType l ':<>: 'Text ", +infinity)"
  EndsErrorMessage (CO l r) = 'Text "[" ':<>: 'ShowType l ':<>: 'Text ", " ':<>: 'ShowType r ':<>: 'Text ")"
  EndsErrorMessage (CuC r) = 'Text "[-infinity, " ':<>: 'ShowType r ':<>: 'Text "]"
  EndsErrorMessage (CuO r) = 'Text "[-infinity, " ':<>: 'ShowType r ':<>: 'Text ")"
  EndsErrorMessage CuCu = 'Text "[-infinity, +infinity]"
  EndsErrorMessage CuOu = 'Text "[-infinity, +infinity)"
  EndsErrorMessage (OC l r) = 'Text "(" ':<>: 'ShowType l ':<>: 'Text ", " ':<>: 'ShowType r ':<>: 'Text "]"
  EndsErrorMessage (OO l r) = 'Text "(" ':<>: 'ShowType l ':<>: 'Text ", " ':<>: 'ShowType r ':<>: 'Text ")"
  EndsErrorMessage (OCu l) = 'Text "(" ':<>: 'ShowType l ':<>: 'Text ", +infinity]"
  EndsErrorMessage (OOu l) = 'Text "(" ':<>: 'ShowType l ':<>: 'Text ", +infinity)"
  EndsErrorMessage (OuC r) = 'Text "(-infinity, " ':<>: 'ShowType r ':<>: 'Text "]"
  EndsErrorMessage (OuO r) = 'Text "(-infinity, " ':<>: 'ShowType r ':<>: 'Text ")"
  EndsErrorMessage OuCu = 'Text "(-infinity, +infinity]"
  EndsErrorMessage OuOu = 'Text "(-infinity, +infinity)"

proveContains
  :: forall {l} {r} {k} (e :: Ends l r) (x :: k) (a :: Type)
  .  (KnownEnds e a, KnownNum x a, Ord a, GetNegInfinity a, GetPosInfinity a)
  => Proxy e
  -> Proxy x
  -> Proxy a
  -> Maybe (Dict (Contains e x))
proveContains pe px _ = do
  guard $ contains (endsVal pe) (numVal px :: a)
  pure (unsafeCoerce (Dict @()))

-- | @'contains' ends a@ says whether the interval @ends@ contain @a@.
contains
  :: forall a
  .  ( Ord a
     , GetNegInfinity a
     , GetPosInfinity a )
  => Ends a a
  -> a
  -> Bool
contains (Ends el er) = \a -> fl a && fr a
  where
    fl :: a -> Bool
    fl = case el of
      C l -> \a -> l <= a
      Cu  -> \_ -> True
      O l -> \a -> l <  a
      Ou  -> ifNegInfinity @a (negInfinity <) (const True)
    fr :: a -> Bool
    fr = case er of
      C r -> \a -> a <= r
      O r -> \a -> a <  r
      Cu  -> \_ -> True
      Ou  -> ifPosInfinity @a (< posInfinity) (const True)

--------------------------------------------------------------------------------

-- | Whether @l@, if any, is at most @r@, if any.
class Ordered (e :: Ends l r)
instance l <= r => Ordered (CC l r)
instance l <= r => Ordered (CO l r)
instance l <= r => Ordered (OC l r)
instance l <= l => Ordered (OO l r)
instance {-# OVERLAPPABLE #-} Ordered e

--------------------------------------------------------------------------------

{- OK BUT NOT USED

type EndsNotEmpty :: Ends l r -> Constraint
type family EndsNotEmpty e where
  EndsNotEmpty (CC l r) = l <= r
  EndsNotEmpty (CO l r) = l <  r
  EndsNotEmpty (OC l r) = l <  r
  EndsNotEmpty (OO l r) = l <  l
  EndsNotEmpty _        = ()


type Simpler :: a -> b
type family Simpler a :: b where
  Simpler (a :: Rat) = SimplerRatSimplified (Simplify a)
  Simpler (n :: Nat) = n
  Simpler ('Neg 0 :: TInt) = 0
  Simpler ('Pos n :: TInt) = n

type SimplerRatSimplified :: Rat -> b
type family SimplerRatSimplified a :: b where
  SimplerRatSimplified (n ':% 1) = Simpler n
  SimplerRatSimplified ((0 :: Nat) ':% _) = 0
  SimplerRatSimplified (('Neg 0 :: TInt) ':% _) = 0
  SimplerRatSimplified (('Pos 0 :: TInt) ':% _) = 0
  SimplerRatSimplified r = r
-}

transSub :: forall x y z. (x `SubOf` y, y `SubOf` z) :- (x `SubOf` z)
transSub = Sub (unsafeCoerce (Dict @()))

supContains :: forall x y z. (y `Contains` x, y `SubOf` z) :- (z `Contains` x)
supContains = Sub (unsafeCoerce (Dict @()))

--------------------------------------------------------------------------------

-- | @'Interval' e a@ is the type for values of type @a@ within the interval
-- endpoints @e@.
newtype Interval (e :: Ends l r) (a :: Type)
  = UnsafeInterval a
  -- ^ To construct safely, ensure that @'KnownInterval' e a@ is satisfied.
  deriving newtype (Eq, Ord, Show)

{--
-- TODO: Doesn't compile due to usage of TypeEnds type-family.
deriving newtype instance
  ( TypeEnds a ~ e
  , KnownInterval e a
  , Generic a
  ) => Generic (Interval e a)

deriving newtype instance
  ( TypeEnds a ~ e
  , KnownInterval e a
  , Storable a
  ) => Storable (Interval e a)
--}

instance forall e a.
  ( KnownInterval e a
  , Ord a
  , Read a
  ) => Read (Interval e a) where
  readPrec = do
    a :: a <- readPrec
    maybe (fail "intervalFrom") pure (intervalFrom a)

unInterval :: forall e a. Interval e a -> a
unInterval = coerce
{-# INLINE unInterval #-}

interval :: forall a. KnownTypeInterval a => a -> TypeInterval a
interval = coerce
{-# INLINE interval #-}

intervalVal
  :: forall t e a
  .  ( KnownInterval e a
     , Contains e t
     , KnownNum t a )
  => Proxy t
  -> Interval e a
intervalVal = UnsafeInterval . numVal
{-# INLINE intervalVal #-}

--------------------------------------------------------------------------------

class
  ( e `SubOf` e
  , e `SubOf` TypeEnds a
  , Ordered e
  , KnownEnds e a
  , IntervalEnds' e a ~ e
  , IntervalType' e a ~ a
  , GetNegInfinity a
  , GetPosInfinity a
  ) => KnownInterval (e :: Ends l r) (a :: Type) where
  -- | Associated type depending on both @e@ and @a@, so that
  -- 'KnownInterval''s superclasses can be enforced.
  type IntervalEnds' e a :: Ends l r
  type IntervalEnds' e _ = e
  -- | Associated type depending on both @e@ and @a@, so that
  -- 'KnownInterval''s superclasses can be enforced.
  type IntervalType' e a :: Type
  type IntervalType' _ a = a

instance
  ( e `SubOf` e
  , e `SubOf` TypeEnds a
  , Ordered e
  , KnownEnds e a
  , GetNegInfinity a
  , GetPosInfinity a
  ) => KnownInterval e a

type family IntervalEnds (i :: Type) :: Ends l r where
  -- See comment on 'IntervalEnds\''
  IntervalEnds (Interval e a) = IntervalEnds' e a

type family IntervalType (i :: Type) :: Type where
  -- See comment on 'IntervalType\''
  IntervalType (Interval e a) = IntervalType' e a

--------------------------------------------------------------------------------

-- | @
-- 'unInterval'' == 'unInterval' . 'upcast''
-- @
unInterval'
  :: forall e au ad
  .  Upcast e au e ad
  => Interval e ad
  -> au
unInterval' = unInterval . upcast'
{-# INLINE unInterval' #-}

-- | @
-- 'unInterval' == fmap 'unInterval' . 'downcast''
-- @
fromInterval :: forall e au ad. Downcast e au e ad => Interval e au -> Maybe ad
fromInterval = fmap unInterval . downcast'
{-# INLINE fromInterval #-}

-- | @
-- 'interval'' == 'upcast' . 'interval'
-- @
interval'
  :: forall e au ad
  .  ( Upcast e au (TypeEnds ad) ad
     , KnownTypeInterval ad )
  => ad
  -> Interval e au
interval' = (upcast :: TypeInterval ad -> Interval e au)
          . (interval :: ad -> TypeInterval ad)
{-# INLINE interval' #-}

intervalFrom
  :: forall e a
  .  ( KnownInterval e a
     , Ord a )
  => a
  -> Maybe (Interval e a)
intervalFrom =
  let f = contains (endsVal (Proxy @e))
  in \a -> if f a then Just (UnsafeInterval a) else Nothing

-- | @
-- 'intervalFrom' = 'downcast'' <=< 'intervalFrom'
-- @
intervalFrom'
  :: forall e au ad
  .  ( Downcast e au e ad
     , KnownInterval e au
     , Ord au )
  => au
  -> Maybe (Interval e ad)
intervalFrom' = downcast' <=< intervalFrom
{-# INLINE intervalFrom' #-}

--------------------------------------------------------------------------------

class KnownInterval e a => MinInterval e a where
  -- | Minimum possible @'Interval' e a@, if any.
  minInterval :: Interval e a

instance forall l r a.
  ( l <= r
  , Contains (TypeEnds a) l
  , KnownNum l a
  , KnownInterval (CC l r) a
  ) => MinInterval (CC l r) a where
  minInterval = UnsafeInterval (numVal (Proxy @l))

instance forall l r a.
  ( l < r
  , Contains (TypeEnds a) l
  , KnownNum l a
  , KnownInterval (CO l r) a
  ) => MinInterval (CO l r) a where
  minInterval = UnsafeInterval (numVal (Proxy @l))

instance forall kl kr (l :: kl) a.
  ( KnownNum l a
  , Contains (TypeEnds a) l
  , KnownInterval (CCu l :: Ends kl kr) a
  ) => MinInterval (CCu l :: Ends kl kr) a where
  minInterval = UnsafeInterval (numVal (Proxy @l))

instance forall kl kr (l :: kl) a.
  ( KnownNum l a
  , Contains (TypeEnds a) l
  , KnownInterval (COu l :: Ends kl kr) a
  ) => MinInterval (COu l :: Ends kl kr) a where
  minInterval = UnsafeInterval (numVal (Proxy @l))

instance forall l r a.
  ( Succ l <= r
  , Contains (TypeEnds a) (Succ l)
  , KnownNum (Succ l) a
  , KnownInterval (OC l r) a
  , Integral a
  ) => MinInterval (OC l r) a where
  minInterval = UnsafeInterval (numVal (Proxy @(Succ l)))

instance forall l r a.
  ( Succ l < r
  , Contains (TypeEnds a) (Succ l)
  , KnownNum (Succ l) a
  , KnownInterval (OO l r) a
  , Integral a
  ) => MinInterval (OO l r) a where
  minInterval = UnsafeInterval (numVal (Proxy @(Succ l)))

instance forall kl kr (l :: kl) a.
  ( KnownNum (Succ l) a
  , Contains (TypeEnds a) (Succ l)
  , KnownInterval (OCu l :: Ends kl kr) a
  , Integral a
  ) => MinInterval (OCu l :: Ends kl kr) a where
  minInterval = UnsafeInterval (numVal (Proxy @(Succ l)))

instance forall kl kr (l :: kl) a.
  ( KnownNum (Succ l) a
  , Contains (TypeEnds a) (Succ l)
  , KnownInterval (OOu l :: Ends kl kr) a
  , Integral a
  ) => MinInterval (OOu l :: Ends kl kr) a where
  minInterval = UnsafeInterval (numVal (Proxy @(Succ l)))

instance forall kl kr (er :: End kr) a.
  ( KnownNum ('Neg 1 ':% 0) a
  , Contains (TypeEnds a) ('Neg 1 ':% 0)
  , KnownInterval ('Ends 'Cu er :: Ends kl kr) a
  ) => MinInterval ('Ends 'Cu er :: Ends kl kr) a where
  minInterval = UnsafeInterval (numVal (Proxy @('Neg 1 ':% 0)))

--------------------------------------------------------------------------------

class KnownInterval e a => MaxInterval e a where
  -- | Maximum possible @'Interval' e a@, if any.
  maxInterval :: Interval e a

instance forall l r a.
  ( l <= r
  , Contains (TypeEnds a) r
  , KnownNum r a
  , KnownInterval (CC l r) a
  ) => MaxInterval (CC l r) a where
  maxInterval = UnsafeInterval (numVal (Proxy @r))

instance forall l r a.
  ( l <= Pred r
  , Contains (TypeEnds a) (Pred r)
  , KnownNum (Pred r) a
  , KnownInterval (CO l r) a
  ) => MaxInterval (CO l r) a where
  maxInterval = UnsafeInterval (numVal (Proxy @(Pred r)))

instance forall l r a.
  ( l < r
  , Contains (TypeEnds a) r
  , KnownNum r a
  , KnownInterval (OC l r) a
  , Integral a
  ) => MaxInterval (OC l r) a where
  maxInterval = UnsafeInterval (numVal (Proxy @r))

instance forall l r a.
  ( l < Pred r
  , KnownNum (Pred r) a
  , KnownInterval (OO l r) a
  , Contains (TypeEnds a) (Pred r)
  , Integral a
  ) => MaxInterval (OO l r) a where
  maxInterval = UnsafeInterval (numVal (Proxy @(Pred r)))

instance forall kl kr (el :: End kl) a.
  ( KnownNum (1 ':% 0) a
  , Contains (TypeEnds a) (1 ':% 0)
  , KnownInterval ('Ends el 'Cu :: Ends kl kr) a
  ) => MaxInterval ('Ends el 'Cu :: Ends kl kr) a where
  maxInterval = UnsafeInterval (numVal (Proxy @(1 ':% 0)))

instance forall kl kr (r :: kr) a.
  ( KnownNum r a
  , Contains (TypeEnds a) r
  , KnownInterval (CuC r :: Ends kl kr) a
  ) => MaxInterval (CuC r :: Ends kl kr) a where
  maxInterval = UnsafeInterval (numVal (Proxy @r))

instance forall kl kr (r :: kr) a.
  ( KnownNum (Pred r) a
  , Contains (TypeEnds a) (Pred r)
  , KnownInterval (CuO r :: Ends kl kr) a
  ) => MaxInterval (CuO r :: Ends kl kr) a where
  maxInterval = UnsafeInterval (numVal (Proxy @(Pred r)))

instance forall kl kr (r :: kr) a.
  ( KnownNum r a
  , Contains (TypeEnds a) r
  , KnownInterval (OuC r :: Ends kl kr) a
  ) => MaxInterval (OuC r :: Ends kl kr) a where
  maxInterval = UnsafeInterval (numVal (Proxy @r))

instance forall kl kr (r :: kr) a.
  ( KnownNum (Pred r) a
  , Contains (TypeEnds a) (Pred r)
  , KnownInterval (OuO r :: Ends kl kr) a
  ) => MaxInterval (OuO r :: Ends kl kr) a where
  maxInterval = UnsafeInterval (numVal (Proxy @(Pred r)))

--------------------------------------------------------------------------------


class
  ( KnownInterval eu au
  , ed `SubOf` eu
  ) => Upcast eu au ed ad where
  -- | Roundtrip law:
  --
  -- @
  -- 'downcast' ('upcast' x :: 'Interval' lu ru au)
  --         == 'Just' (x :: 'Interval' ld rd ad)
  -- @
  --
  -- Upcast Identity law:
  --
  -- @
  -- 'upcast' (x :: 'Interval' l r a)
  --     == (x :: 'Interval' l r a)
  -- @
  --
  -- Downcast Identity law:
  --
  -- @
  -- 'downcast' (x :: 'Interval' l r a)
  --  == 'Just' (x :: 'Interval' l r a)
  -- @
  upcast :: Interval ed ad -> Interval eu au
  -- | Default implementation for the common case of
  -- upcasting an @'Integral' ad@ to a @'Num' au@.
  default upcast
    :: ( KnownInterval eu au
       , ed `SubOf` eu
       , Integral ad
       , Num au )
    => Interval ed ad
    -> Interval eu au
  upcast = upcastIntegral
  {-# INLINE upcast #-}

upcastEnd
  :: forall eu ed a
  .  Upcast eu a ed a
  => Interval ed a
  -> Interval eu a
upcastEnd = upcast
{-# INLINE upcastEnd #-}

upcast'
  :: forall e au ad
  .  Upcast e au e ad
  => Interval e ad
  -> Interval e au
upcast' = upcast
{-# INLINE upcast' #-}

-- | Like 'upcast', constrained to the the common case of upcasting
-- an @'Integral' ad@ to a @'Num' au@. This can be used as the
-- implementation for the 'upcast' method.
upcastIntegral
  :: forall eu au ed ad
  .  ( KnownInterval eu au
     , ed `SubOf` eu
     , Integral ad
     , Num au )
  => Interval ed ad
  -> Interval eu au
upcastIntegral
  = (UnsafeInterval :: au -> Interval eu au)
  . (fromIntegral :: ad -> au)
  . (unInterval :: Interval ed ad -> ad)

-- | Like 'upcast', constrained to the the common case of upcasting
-- a @'Real' ad@ to a @'Fractional' au@. This can be used as the
-- implementation for the 'upcast' method.
--
-- /WARNING/ This relies on
-- @('fromRational' . 'toRational' :: ad -> au)@, which
-- may or may not be ideal depending on the choice of @ad@ and @ad@.
upcastReal
  :: forall eu au ed ad
  .  ( KnownInterval eu au
     , ed `SubOf` eu
     , Real ad
     , Fractional au )
  => Interval ed ad
  -> Interval eu au
upcastReal
  = (UnsafeInterval :: au -> Interval eu au)
  . (fromRational :: Rational -> au)
  . (toRational :: ad -> Rational)
  . (unInterval :: Interval ed ad -> ad)

-- | Like 'upcast', constrained to the the common case of upcasting
-- a @'RealFloat' ad@ to a @'Fractional' au@. This can be used as the
-- implementation for the 'upcast' method.
--
-- /WARNING/ For non-infinite @ad@ values, this relies on
-- @('fromRational' . 'toRational' :: ad -> au)@, which
-- may or may not be ideal depending on the choice of @ad@ and @ad@.
upcastRealFloat
  :: forall eu au ed ad
  .  ( KnownInterval eu au
     , ed `SubOf` eu
     , RealFloat ad
     , Fractional au
     , HasNegInfinity au
     , HasPosInfinity au )
  => Interval ed ad
  -> Interval eu au
upcastRealFloat = \i -> UnsafeInterval $ case unInterval i of
  f | isInfinite f -> if f < 0 then negInfinity else posInfinity
    | otherwise    -> fromRational (toRational f)

instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Integer
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Natural
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Int
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Int8
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Int16
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Int32
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Int64
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Word
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Word8
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Word16
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Word32
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed Word64
instance (KnownInterval eu au, ed `SubOf` eu, Num au) => Upcast eu au ed CSize

instance (KnownInterval eu au, ed `SubOf` eu, Fractional au)
  => Upcast eu au ed (Ratio Natural) where
  upcast = upcastReal
  {-# INLINE upcast #-}

instance (KnownInterval eu au, ed `SubOf` eu, Fractional au)
  => Upcast eu au ed Rational where
  upcast = upcastReal
  {-# INLINE upcast #-}

instance ( KnownInterval eu au, ed `SubOf` eu, Fractional au
         , HasNegInfinity au, HasPosInfinity au )
  => Upcast eu au ed Float where
  upcast = upcastRealFloat
  {-# INLINE upcast #-}
instance ( KnownInterval eu au, ed `SubOf` eu, Fractional au
         , HasNegInfinity au, HasPosInfinity au )
  => Upcast eu au ed Double where
  upcast = upcastRealFloat
  {-# INLINE upcast #-}

--------------------------------------------------------------------------------

class
  ( KnownInterval ed ad
  ) => Downcast eu au ed ad where
  -- | Roundtrip law:
  --
  -- @
  -- 'downcast' ('upcast' x :: 'Interval' lu ru au)
  --         == 'Just' (x :: 'Interval' ld rd ad)
  -- @
  --
  -- Upcast Identity law:
  --
  -- @
  -- 'upcast' (x :: 'Interval' l r a)
  --     == (x :: 'Interval' l r a)
  -- @
  --
  -- Downcast Identity law:
  --
  -- @
  -- 'downcast' (x :: 'Interval' l r a)
  --  == 'Just' (x :: 'Interval' l r a)
  -- @
  downcast :: Interval eu au -> Maybe (Interval ed ad)
  -- | Default implementation for the common case of
  -- downcasting an @'Integral' ad@ to a @'Num' au@.
  default downcast
    :: ( KnownInterval ed ad
       , Integral au
       , Num ad
       , Ord ad )
    => Interval eu au
    -> Maybe (Interval ed ad)
  downcast = downcastIntegral
  {-# INLINE downcast #-}

downcastEnd
  :: forall eu ed a
  .  Downcast eu a ed a
  => Interval eu a
  -> Maybe (Interval ed a)
downcastEnd = downcast
{-# INLINE downcastEnd #-}

downcast'
  :: forall e au ad
  .  Downcast e au e ad
  => Interval e au
  -> Maybe (Interval e ad)
downcast' = downcast
{-# INLINE downcast' #-}

downcastIntegral
  :: forall eu au ed ad
  .  ( KnownInterval ed ad
     , Integral au
     , Num ad
     , Ord ad )
  => Interval eu au
  -> Maybe (Interval ed ad)
downcastIntegral
  = (intervalFrom :: ad -> Maybe (Interval ed ad))
  . (fromIntegral :: au -> ad)
  . (unInterval :: Interval eu au -> au)
{-# INLINE downcastIntegral #-}

downcastReal
  :: forall eu au ed ad
  .  ( KnownInterval ed ad
     , Real au
     , Fractional ad
     , Ord ad )
  => Interval eu au
  -> Maybe (Interval ed ad)
downcastReal
  = (intervalFrom :: ad -> Maybe (Interval ed ad))
  . (fromRational :: Rational -> ad)
  . (toRational :: au -> Rational)
  . (unInterval :: Interval eu au -> au)
{-# INLINE downcastReal #-}

downcastRealFloat
  :: forall eu au ed ad
  .  ( KnownInterval ed ad
     , RealFloat au
     , Fractional ad
     , GetNegInfinity ad
     , GetPosInfinity ad
     , Ord ad )
  => Interval eu au
  -> Maybe (Interval ed ad)
downcastRealFloat = \i -> case unInterval i of
    f | isInfinite f -> if f < 0 then yni else ypi
      | otherwise    -> intervalFrom (fromRational (toRational f))
  where
    yni = ifNegInfinity @ad (intervalFrom negInfinity) Nothing
    ypi = ifPosInfinity @ad (intervalFrom posInfinity) Nothing

instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Integer ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Natural ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Int     ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Int8    ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Int16   ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Int32   ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Int64   ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Word    ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Word8   ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Word16  ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Word32  ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu Word64  ed ad
instance (KnownInterval ed ad, Num ad, Ord ad) => Downcast eu CSize   ed ad

instance (KnownInterval ed ad, Fractional ad, Ord ad)
  => Downcast eu Rational ed ad where
  downcast = downcastReal
  {-# INLINE downcast #-}

instance (KnownInterval ed ad, Fractional ad, Ord ad)
  => Downcast eu (Ratio Natural) ed ad where
  downcast = downcastReal
  {-# INLINE downcast #-}

instance (KnownInterval ed ad, Fractional ad, Ord ad)
  => Downcast eu Float ed ad where
  downcast = downcastRealFloat
  {-# INLINE downcast #-}
instance (KnownInterval ed ad, Fractional ad, Ord ad)
  => Downcast eu Double ed ad where
  downcast = downcastRealFloat
  {-# INLINE downcast #-}

--------------------------------------------------------------------------------

-- type KindOf (a :: k) = k
--
-- type AsKindOf (a :: k) (b :: k) = a
--
-- type Compare :: ka -> kb -> Ordering
-- type Compare a b = If (a <=? b) (If (b <=? a) 'EQ 'LT) 'GT

infixl 4 <?, >?, >=?
infixl 4 <=, <, >, >=

type (a :: ka) >=? (b :: kb) =      b <=? a  :: Bool
type (a :: ka) <?  (b :: kb) = Not (b <=? a) :: Bool
type (a :: ka) >?  (b :: kb) = Not (a <=? b) :: Bool

type family (a :: ka) <= (b :: kb) :: Constraint where
  a <= b = If (a <=? b) (() :: Constraint)
   (TypeError ('ShowType a ':<>: 'Text " ≰ " ':<>: 'ShowType b))
type family (a :: ka) < (b :: kb) :: Constraint where
  a < b = If (a <? b) (() :: Constraint)
   (TypeError ('ShowType a ':<>: 'Text " ≮ " ':<>: 'ShowType b))
type family (a :: ka) > (b :: kb) :: Constraint where
  a > b = If (a >? b) (() :: Constraint)
   (TypeError ('ShowType a ':<>: 'Text " ≯ " ':<>: 'ShowType b))
type family (a :: ka) >= (b :: kb) :: Constraint where
  a >= b = If (a >=? b) (() :: Constraint)
    (TypeError ('ShowType a ':<>: 'Text " ≱ " ':<>: 'ShowType b))

type Succ :: k -> k
type family Succ x where
  Succ (x :: Nat)  = x + 1
  Succ (x :: TInt) = x + 1

type Pred :: k -> k
type family Pred x where
  Pred (0 :: Nat)  = TypeError ('Text "Nat underflow")
  Pred (x :: Nat)  = x - 1
  Pred (x :: TInt) = x - 1

type family Denominator (r :: Rat) :: Nat where Denominator (_ ':% d) = d

--------------------------------------------------------------------------------

-- | This type family seems to be necessary for 'TypeEnds' to work.
type family MinBoundKind (a :: Type) :: k
-- | Type-level version of @'minBound' :: a@.
type MinBound (a :: Type) = MinBoundAux (EndsL (TypeEnds a)) :: MinBoundKind a
-- | Internal.
type family MinBoundAux (er :: End r) :: r where MinBoundAux ('C x) = x

-- This type family seems to be necessary for 'TypeEnds' to work.
type family MaxBoundKind (a :: Type) :: k
-- | Type-level version of @'maxBound' :: a@.
type MaxBound (a :: Type) = MaxBoundAux (EndsR (TypeEnds a)) :: MaxBoundKind a
-- | Internal.
type family MaxBoundAux (er :: End r) :: r where MaxBoundAux ('C x) = x

-- | Maximum interval ends for a particuar type @a@.
type family TypeEnds (a :: Type) :: Ends (MinBoundKind a) (MaxBoundKind a)

-- | @'TypeInterval' a@ is isomorphic to @a@.
type TypeInterval (a :: Type) = Interval (TypeEnds a) a :: Type

class    KnownInterval (TypeEnds a) a => KnownTypeInterval (a :: Type)
instance KnownInterval (TypeEnds a) a => KnownTypeInterval (a :: Type)

--------------------------------------------------------------------------------

type instance TypeEnds     Natural = COu 0
type instance MinBoundKind Natural = Nat

type instance TypeEnds Integer = OuOu

type instance TypeEnds Rational = OuOu

type instance TypeEnds     (Ratio Natural) = COu 0
type instance MinBoundKind (Ratio Natural) = Nat

type instance MinBoundKind Word = Nat
type instance MaxBoundKind Word = Nat

type instance MinBoundKind Int = TInt
type instance MaxBoundKind Int = Nat

type instance TypeEnds     Word8 = CC 0 255
type instance MinBoundKind Word8 = Nat
type instance MaxBoundKind Word8 = Nat

type instance TypeEnds     Word16 = CC 0 65535
type instance MinBoundKind Word16 = Nat
type instance MaxBoundKind Word16 = Nat

type instance TypeEnds     Word32 = CC 0 4294967295
type instance MinBoundKind Word32 = Nat
type instance MaxBoundKind Word32 = Nat

type instance TypeEnds     Word64 = CC 0 18446744073709551615
type instance MinBoundKind Word64 = Nat
type instance MaxBoundKind Word64 = Nat

type instance TypeEnds     Int8 = CC ('Neg 128) 127
type instance MinBoundKind Int8 = TInt
type instance MaxBoundKind Int8 = Nat

type instance TypeEnds     Int16 = CC ('Neg 32768) 32767
type instance MinBoundKind Int16 = TInt
type instance MaxBoundKind Int16 = Nat

type instance TypeEnds     Int32 = CC ('Neg 2147483648) 2147483647
type instance MinBoundKind Int32 = TInt
type instance MaxBoundKind Int32 = Nat

type instance TypeEnds     Int64 = CC ('Neg 9223372036854775808) 9223372036854775807
type instance MinBoundKind Int64 = TInt
type instance MaxBoundKind Int64 = Nat

type instance TypeEnds     Float = CuCu
type instance MinBoundKind Float = Rat
type instance MaxBoundKind Float = Rat
instance GetNegInfinity Float
instance HasNegInfinity Float where negInfinity = -1/0
instance GetPosInfinity Float
instance HasPosInfinity Float where posInfinity =  1/0

type instance TypeEnds     Double = CuCu
type instance MinBoundKind Double = Rat
type instance MaxBoundKind Double = Rat
instance GetNegInfinity Double
instance HasNegInfinity Double where negInfinity = -1/0
instance GetPosInfinity Double
instance HasPosInfinity Double where posInfinity =  1/0

type instance TypeEnds     CSize = TypeEnds     Word
type instance MinBoundKind CSize = MinBoundKind Word
type instance MaxBoundKind CSize = MaxBoundKind Word

#if WORD_SIZE_IN_BITS == 64
type instance TypeEnds Int  = TypeEnds Int64
type instance TypeEnds Word = TypeEnds Word64
#elif WORD_SIZE_IN_BITS == 32
type instance TypeEnds Int  = TypeEnds Int32
type instance TypeEnds Word = TypeEnds Word32
#else
#  error "Unexpected WORD_SIZE_IN_BYTES"
#endif


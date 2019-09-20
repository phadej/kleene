{-# LANGUAGE Safe #-}
module Kleene.Internal.Partition where

import Data.Semigroup (Semigroup (..))
import Prelude ()
import Prelude.Compat

import Data.Foldable      (toList)
import Data.List.NonEmpty (NonEmpty (..))
import Data.RangeSet.Map  (RSet)
import Data.Set           (Set)

import qualified Data.Function.Step.Discrete.Closed as SF
import qualified Data.List.NonEmpty                 as NE
import qualified Data.RangeSet.Map                  as RSet
import qualified Data.Set                           as Set

import Test.QuickCheck

-- | 'Partition' devides type into disjoint connected partitions.
--
-- /Note:/ we could have non-connecter partitions too,
-- but that would be more complicated.
-- This variant is correct by construction, but less precise.
--
-- It's enought to store last element of each piece.
--
-- @'Partition' (fromList [x1, x2, x3]) :: 'Partition' s@ describes a partition of /Set/ @s@, as
--
-- \[
-- \{ x \mid x \le x_1 \} \cup
-- \{ x \mid x_1 < x \le x_2 \} \cup
-- \{ x \mid x_2 < x \le x_3 \} \cup
-- \{ x \mid x_3 < x \}
-- \]
--
-- /Note:/ it's enough to check upper bound conditions only if checks are performed in order.
--
-- /Invariant:/ 'maxBound' is not in the set.
--
newtype Partition a  = Partition { unPartition :: Set a }
  deriving (Eq, Ord)

-- | Check invariant.
invariant :: (Ord a, Bounded a) => Partition a -> Bool
invariant (Partition xs) = Set.notMember maxBound xs

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Show a => Show (Partition a) where
    showsPrec d (Partition xs)
        = showParen (d > 10)
        $ showString "fromSeparators "
        . showsPrec 11 (Set.toList xs)

-- | prop> invariant (asPartitionChar p)
instance (Enum a, Bounded a, Ord a, Arbitrary a) => Arbitrary (Partition a) where
    arbitrary = fromSeparators <$> arbitrary

-- | See 'wedge'.
instance (Enum a, Bounded a, Ord a) => Semigroup (Partition a) where
    (<>) = wedge

instance (Enum a, Bounded a, Ord a) => Monoid (Partition a) where
    mempty = whole
    mappend = (<>)

-------------------------------------------------------------------------------
-- Constructors
-------------------------------------------------------------------------------

fromSeparators :: (Enum a, Bounded a, Ord a) => [a] -> Partition a
fromSeparators = Partition . Set.fromList . filter (/= maxBound)

-- | Construct 'Partition' from list of 'RSet's.
--
-- RSet intervals are closed on both sides.
fromRSets :: (Enum a, Bounded a, Ord a) => [RSet a] -> Partition a
fromRSets rs = Partition $ Set.fromList $ concat
    [ (if x == minBound then [] else [pred x]) ++
      (if y == maxBound then [] else [y])
    | r <- rs
    , (x, y) <- RSet.toRangeList r
    ]

fromRSet :: (Enum a, Bounded a, Ord a) => RSet a -> Partition a
fromRSet r
    | r == RSet.empty = whole
    | r == RSet.full  = whole
    | otherwise       = fromRSets [r]

whole :: Partition a
whole = Partition Set.empty

-------------------------------------------------------------------------------
-- Querying
-------------------------------------------------------------------------------

-- | Count of sets in a 'Partition'.
--
-- >>> size whole
-- 1
--
-- >>> size $ split (10 :: Word8)
-- 2
--
-- prop> size (asPartitionChar p) >= 1
--
size :: Partition a -> Int
size (Partition xs) = 1 + length xs

-- | Extract examples from each subset in a 'Partition'.
--
-- >>> examples $ split (10 :: Word8)
-- fromList [10,255]
--
-- >>> examples $ split (10 :: Word8) <> split 20
-- fromList [10,20,255]
--
-- prop> invariant p ==> size (asPartitionChar p) === length (examples p)
--
examples :: (Bounded a, Enum a, Ord a) => Partition a -> Set a
examples (Partition xs) = Set.insert maxBound xs

-- |
--
-- prop> all (uncurry (<=)) $ intervals $ asPartitionChar p
intervals :: (Enum a, Bounded a, Ord a) => Partition a -> NonEmpty (a, a)
intervals (Partition xs) = go minBound (toList xs) where
    go x []       = (x, maxBound) :| []
    go x (y : ys) = (x, y) `NE.cons` go y ys

-------------------------------------------------------------------------------
--
-- Operations
-------------------------------------------------------------------------------

-- | Wedge partitions.
--
-- >>> split (10 :: Word8) <> split 20
-- fromSeparators [10,20]
--
-- prop> whole `wedge` (p :: Partition Char) === p
-- prop> (p :: Partition Char) <> whole === p
-- prop> asPartitionChar p <> q === q <> p
-- prop> asPartitionChar p <> p === p
-- prop> invariant $ asPartitionChar p <> q
--
wedge :: Ord a => Partition a -> Partition a -> Partition a
wedge (Partition as) (Partition bs) = Partition (Set.union as bs)

-- | Simplest partition: given @x@ partition space into @[min..x) and [x .. max]@
--
-- >>> split (128 :: Word8)
-- fromSeparators [128]
--
split :: (Enum a, Bounded a, Eq a) => a -> Partition a
split x
    | x == minBound = Partition Set.empty
    | otherwise     = Partition (Set.singleton x)

-------------------------------------------------------------------------------
-- Conversion
-------------------------------------------------------------------------------

-- | Make a step function.
toSF :: (Enum a, Bounded a, Ord a) => (a -> b) -> Partition a -> SF.SF a b
toSF f (Partition p) = SF.fromList
    (map (\k -> (k, f k)) $ toList as)
    (f maxBound)
  where
    as = toList p

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> import Data.Word
-- >>> import Test.QuickCheck ((===))
--
-- >>> let asPartitionChar :: Partition Char -> Partition Char; asPartitionChar = id
-- >>> instance (Ord a, Enum a, Arbitrary a) => Arbitrary (RSet a) where arbitrary = fmap RSet.fromRangeList arbitrary

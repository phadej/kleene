{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
module Kleene.Classes where

import Prelude ()
import Prelude.Compat

import Algebra.Lattice                    (Lattice (..))
import Data.Char                          (ord)
import Data.Foldable                      (toList)
import Data.Function.Step.Discrete.Closed (SF)
import Data.Map                           (Map)
import Data.Maybe                         (mapMaybe)
import Data.RangeSet.Map                  (RSet)
import Data.Word                          (Word8)

import qualified Data.ByteString   as BS
import qualified Data.RangeSet.Map as RSet

import Kleene.Internal.Sets (dotRSet)

-- | Kleene algebra.
--
-- If 'k' is 'Monoid' it's expected that @'appends' = 'mappend'@;
-- if 'k' is 'Algebra.Lattice.Lattice' it's expected that @'unions' = 'Algebra.Lattice.joins'@.
--
-- [Wikipedia: Kleene Algebra](https://en.wikipedia.org/wiki/Kleene_algebra).
--
class Kleene k where
    -- | Empty regex. Doesn't accept anything.
    empty :: k

    -- | Empty string. /Note:/ different than 'empty'.
    eps :: k

    -- | Concatenation.
    appends :: [k] -> k

    -- | Union.
    unions :: [k] -> k

    -- | Kleene star.
    star :: k -> k

class Kleene k => CharKleene c k | k -> c where
    -- | Single character
    char :: c -> k

    string :: [c] -> k
    string = appends . map char

-- | One of the characters.
oneof :: (CharKleene c k, Foldable f) => f c -> k
oneof = unions . map char . toList

class CharKleene c k => FiniteKleene c k | k -> c where
    -- | Everything. \(\Sigma^\star\).
    everything :: k
    everything = star anyChar

    -- | @'charRange' 'a' 'z' = ^[a-z]$@.
    charRange :: c -> c -> k

    -- | Generalisation of 'charRange'.
    fromRSet :: RSet c -> k

    -- | @.@ Every character except new line @\\n@.
    dot :: c ~ Char => k
    dot = fromRSet dotRSet

    -- | Any character. /Note:/ different than 'dot'!
    anyChar :: k

    notChar :: c -> k
    default notChar :: (Ord c, Enum c, Bounded c) => c -> k
    notChar = fromRSet . RSet.complement . RSet.singleton

class Derivate c k | k -> c where
    -- | Does language contain an empty string?
    nullable :: k -> Bool

    -- | Derivative of a language.
    derivate :: c -> k -> k

-- | An @f@ can be used to match on the input.
class Match c k | k -> c where
    match :: k -> [c] -> Bool

    match8 :: c ~ Word8 => k -> BS.ByteString -> Bool
    match8 k = match k . BS.unpack

-- | Equivalence induced by 'Match'.
--
-- /Law:/
--
-- @
-- 'equivalent' re1 re2 <=> forall s. 'match' re1 s == 'match' re1 s
-- @
--
class Match c k => Equivalent c k | k -> c  where
    equivalent :: k -> k -> Bool

-- | Transition map.
class Derivate c k => TransitionMap c k | k -> c where
    transitionMap :: k -> Map k (SF c k)

-- | Complement of the language.
--
-- /Law:/
--
-- @
-- 'match' ('complement' f) xs = 'not' ('match' f) xs
-- @
class Complement c k | k -> c where
    complement :: k -> k

class ToLatin1 k where
    toLatin1 :: k Char -> k Word8

instance ToLatin1 RSet where
    toLatin1 = RSet.fromRangeList . mapMaybe f . RSet.toRangeList where
        f :: (Char, Char) -> Maybe (Word8, Word8)
        f (a, b)
            | ord a >= 256 = Nothing
            | otherwise    = Just (fromIntegral (ord a), fromIntegral (min 255 (ord b)))

disjoint :: (Kleene k, Equivalent c k, Lattice k) => k -> k -> Bool
disjoint a b = equivalent empty (a /\ b)

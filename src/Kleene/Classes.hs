{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
module Kleene.Classes where

import Prelude ()
import Prelude.Compat

import Algebra.Lattice                    (BoundedJoinSemiLattice (..), joins)
import Data.Foldable                      (toList)
import Data.Function.Step.Discrete.Closed (SF)
import Data.Map                           (Map)
import Data.RangeSet.Map                  (RSet)

import Kleene.Internal.Sets (dotRSet)

class (BoundedJoinSemiLattice k, Semigroup k, Monoid k) => Kleene c k | k -> c where
    -- | Empty regex. Doesn't accept anything.
    empty :: k
    empty = bottom

    -- | Empty string. /Note:/ different than 'empty'
    eps :: k
    eps = mempty

    -- | Single character
    char :: c -> k

    -- | Concatenation.
    appends :: [k] -> k
    appends = mconcat

    -- | Union.
    unions :: [k] -> k
    unions = joins

    -- | Kleene star
    star :: k -> k

-- | One of the characters.
oneof :: (Kleene c k, Foldable f) => f c -> k
oneof = unions . map char . toList

class Kleene c k => FiniteKleene c k | k -> c where
    -- | Everything. \(\Sigma^\star\).
    everything :: k
    everything = star anyChar

    -- | @'charRange' 'a' 'z' = ^[a-z]$@.
    charRange :: c -> c -> k

    -- | Generalisation of 'charRange'.
    fromRSet :: RSet c -> k

    -- | @.$. Every character except new line @\\n@.
    dot :: c ~ Char => k
    dot = fromRSet dotRSet

    -- | Any character. /Note:/ different than dot!
    anyChar :: k

class Derivate c k | k -> c where
    -- | Does language contain an empty string?
    nullable :: k -> Bool

    -- | Derivative of a language.
    derivate :: c -> k -> k

-- | An @f@ can be used to match on the input.
class Match c k | k -> c where
    match :: k -> [c] -> Bool

-- | Equivalence induced by 'Matches'.
--
-- /Law:/
--
-- @
-- 'equivalent' re1 re2 <=> forall s. 'matches' re1 s == 'matches' re1 s
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
-- 'matches' ('complement' f) xs = 'not' ('matches' f) xs
-- @
class Complement c k | k -> c where
    complement :: k -> k

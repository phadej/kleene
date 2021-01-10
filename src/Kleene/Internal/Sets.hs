{-# LANGUAGE Safe #-}
{-# OPTIONS_HADDOCK not-home #-}
-- | Character sets.
module Kleene.Internal.Sets (
    dotRSet,
) where

import Data.RangeSet.Map (RSet)

import qualified Data.RangeSet.Map as RSet

-- | All but the newline.
dotRSet :: RSet Char
dotRSet = RSet.full RSet.\\ RSet.singleton '\n'

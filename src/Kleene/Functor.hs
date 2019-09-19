{-# LANGUAGE Safe #-}
module Kleene.Functor (
    K,
    Greediness (..),
    -- * Constructors
    few,
    anyChar,
    oneof,
    char,
    charRange,
    dot,
    everything,
    everything1,
    -- * Queries
    isEmpty,
    isEverything,
    -- * Matching
    match,
    -- * Conversions
    toRE,
    toKleene,
    fromRE,
    toRA,
    ) where

import Kleene.Internal.Functor

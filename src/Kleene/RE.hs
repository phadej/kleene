module Kleene.RE (
    RE (..),
    -- * Construction
    --
    -- | Binary operators are
    --
    -- * '<>' for append
    -- * '\/' for union
    --
    empty,
    eps,
    char,
    charRange,
    anyChar,
    appends,
    unions,
    star,
    string,
    -- * Derivative
    nullable,
    derivate,
    -- * Transition map
    transitionMap,
    leadingChars,
    -- * Equivalence
    equivalent,
    -- * Generation
    generate,
    -- * Other
    isEmpty,
    nullableProof,
    ) where

-- This to include orphans.
import Kleene.Internal.RE
import Kleene.DFA ()

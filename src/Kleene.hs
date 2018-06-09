{-# LANGUAGE Safe #-}
-- | Kleene algebra.
--
-- This package provides means to work with kleene algebra,
-- at the moment specifically concentrating on regular expressions over 'Char'.
--
-- Implements ideas from /Regular-expression derivatives re-examined/ by
-- Scott Owens, John Reppy and Aaron Turon
-- <https://doi.org/10.1017/S0956796808007090>.
--
-- >>> :set -XOverloadedStrings
-- >>> import Algebra.Lattice
-- >>> import Algebra.PartialOrd
-- >>> import Data.Semigroup
-- >>> import Kleene.Internal.Pretty (putPretty)
--
-- "Kleene.RE" module provides 'RE' type. "Kleene.Classes" module provides various
-- classes to work with the type. All of that is re-exported from "Kleene" module.
--
-- First let's construct a regular expression value:
--
-- >>> let re = star "abc" <> "def" <> ("x" \/ "yz") :: RE Char
-- >>> putPretty re
-- ^(abc)*def(x|yz)$
--
-- We can convert it to 'DFA' (there are 8 states)
--
-- >>> let dfa = fromTM re
-- >>> putPretty dfa
-- 0 -> \x -> if
--     | x <= '`'  -> 8
--     | x <= 'a'  -> 5
--     | x <= 'c'  -> 8
--     | x <= 'd'  -> 3
--     | otherwise -> 8
-- 1 -> \x -> if
--     | x <= 'w'  -> 8
--     | x <= 'x'  -> 6
--     | x <= 'y'  -> 7
--     | otherwise -> 8
-- 2 -> ...
-- ...
--
-- It's also possible to graphically visualise DFAs
--
-- @
-- λ> writeFile "example.dot' ('toDot' dfa)
-- %  dot -Tpng -oexample.png example.dot
-- @
--
-- ![example.png](example.png)
--
-- And we can convert back from 'DFA' to 'RE':
--
-- >>> let re' = toKleene dfa :: RE Char
-- >>> putPretty re'
-- ^(a(bca)*bcdefx|defx|(a(bca)*bcdefy|defy)z)$
--
-- As you see, we don't get what we started with. Yet, these
-- regular expressions are 'equivalent';
--
-- >>> equivalent re re'
-- True
--
-- or using 'Equiv' wrapper
--
-- >>> Equiv re == Equiv re'
-- True
--
-- (The paper doesn't outline decision procedure for the equivalence, though
-- it's right there - seems to be fast enough at least for toy examples like
-- here).
--
-- We can use regular expressions to generate word examples in the language:
--
-- >>> import Data.Foldable
-- >>> import qualified Test.QuickCheck as QC
-- >>> import Kleene.RE (generate)
--
-- >>> traverse_ print $ take 5 $ generate (curry QC.choose) 42 re
-- "abcabcabcabcabcabcdefyz"
-- "abcabcabcabcdefyz"
-- "abcabcabcabcabcabcabcabcabcdefx"
-- "abcabcdefx"
-- "abcabcabcabcabcabcdefyz"
--
-- In addition to the "normal" regular expressions, there are /extended regular expressions/.
-- Regular expressions which we can 'complement', and therefore intersect:
--
-- >>> let ere = star "aa" /\ star "aaa" :: ERE Char
-- >>> putPretty ere
-- ^~(~((aa)*)|~((aaa)*))$
--
-- We can convert 'ERE' to 'RE' via 'DFA':
--
-- >>> let re'' = toKleene (fromTM ere) :: RE Char
-- >>> putPretty re''
-- ^(a(aaaaaa)*aaaaa)?$
--
-- Machine works own ways, we don't (always) get as pretty results as we'd like:
--
-- >>> equivalent re'' (star "aaaaaa")
-- True
--
-- Another feature of the library is an 'Applciative' 'Functor',
--
-- >>> import Control.Applicative
-- >>> import qualified Kleene.Functor as F
--
-- >>> let f = (,) <$> many (F.char 'x') <* F.few F.anyChar <*> many (F.char 'z')
-- >>> putPretty f
-- ^x*[^]*z*$
--
-- By relying on <regex-applicative http://hackage.haskell.org/package/regex-applicative> library,
-- we can match and /capture/ with regular expression.
--
-- >>> F.match f "xyyzzz"
-- Just ("x","zzz")
--
-- Where with 'RE' we can only get 'True' or 'False':
--
-- >>> match (F.toRE f) "xyyzzz"
-- True
--
-- Which in this case is not even interesting because:
--
-- >>> equivalent (F.toRE f) everything
-- True
--
-- Converting from 'RE' to 'K' is also possible, which may be handy:
--
-- >>> let g = (,) <$> F.few F.anyChar <*> F.fromRE re''
-- >>> putPretty g
-- ^[^]*(a(aaaaaa)*aaaaa)?$
--
-- >>> F.match g (replicate 20 'a')
-- Just ("aa","aaaaaaaaaaaaaaaaaa")
--
-- We got longest divisible by 6 prefix of as. That's because 'F.fromRE'
-- uses 'many' for 'star'.
--
module Kleene (
    -- * Regular expressions
    RE,
    ERE,

    -- * Equivalance (and partial order)
    Equiv (..),

    -- * Deterministic finite automaton
    DFA (..),
    fromTM,
    fromTMEquiv,
    toKleene,

    -- * Classes
    --
    -- | Most operations are defined in following type-classes.
    --
    -- See "Kleene.RE" module for a specific version with examples.
    Kleene (..),
    Derivate (..),
    Match (..),
    TransitionMap (..),
    Complement (..),

    -- * Functor
    --
    -- | Only the type is exported so it can be referred to.
    --
    -- See "Kleene.Functor" for operations.
    K,
    ) where

import Kleene.Classes
import Kleene.DFA     (DFA (..), fromTM, fromTMEquiv, toKleene)
import Kleene.Equiv
import Kleene.ERE     (ERE)
import Kleene.Functor (K)
import Kleene.RE      (RE)

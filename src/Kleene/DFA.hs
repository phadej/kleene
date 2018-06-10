{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Kleene.DFA (
    DFA (..),
    -- * Mapping
    mapState,
    traverseState,
    -- * Conversions
    fromRE,
    toRE,
    fromERE,
    toERE,
    fromTM,
    fromTMEquiv,
    toKleene,
    toDot,
    toDot',
    ) where

import Prelude ()
import Prelude.Compat

import Algebra.Lattice           ((\/))
import Data.Bifunctor.Compat     (bimap)
import Data.Bitraversable.Compat (bitraverse)
import Data.List                 (intercalate)
import Data.Map                  (Map)
import Data.Maybe                (fromMaybe)
import Data.RangeSet.Map         (RSet)
import Data.Set                  (Set)

import qualified Data.ByteString                    as BS
import qualified Data.Function.Step.Discrete.Closed as SF
import qualified Data.Map                           as Map
import qualified Data.MemoTrie                      as MT
import qualified Data.RangeSet.Map                  as RSet
import qualified Data.Set                           as Set

import           Kleene.Classes
import qualified Kleene.ERE             as ERE
import           Kleene.Internal.Pretty
import qualified Kleene.RE              as RE

-- | Deterministic finite automaton.
--
-- A deterministic finite automaton (DFA) over an alphabet \(\Sigma\) (type
-- variable @c@) is 4-tuple \(Q\), \(q_0\) , \(F\), \(\delta\), where
--
-- * \(Q\) is a finite set of states (subset of 's'),
-- * \(q_0 \in Q\) is the distinguised start state ('dfaInitial'),
-- * \(F \subset Q\) is a set of final (or  accepting) states ('dfaAcceptable'), and
-- * \(\delta : Q \times \Sigma \to Q\) is a function called the state
-- transition function ('dfaTransition').
--
data DFA s c = DFA
    { dfaTransition   :: !(Map s (SF.SF c s))
      -- ^ transition function
    , dfaInitial      :: !s
      -- ^ initial state
    , dfaAcceptable   :: !(Set s)
      -- ^ accept states
    , dfaBlackholes   :: !(Set s)
      -- ^ states we cannot escape
    }
  deriving Show

mapState :: Ord s' => (s -> s') -> DFA s c -> DFA s' c
mapState f (DFA tr ini acc bh) = DFA tr' ini' acc' bh'
  where
    tr'  = Map.fromList . map (bimap f (fmap f)) . Map.toList $ tr
    ini' = f ini
    acc' = Set.map f acc
    bh'  = Set.map f bh

traverseState :: (Applicative f, Ord s') => (s -> f s') -> DFA s c -> f (DFA s' c)
traverseState f (DFA tr ini acc bh) = DFA <$> tr' <*> ini' <*> acc' <*> bh'
  where
    tr'  = fmap Map.fromList $ traverse (bitraverse f (traverse f)) $ Map.toList tr
    ini' = f ini
    acc' = fmap Set.fromList $ traverse f $ Set.toList acc
    bh'  = fmap Set.fromList $ traverse f $ Set.toList bh

-------------------------------------------------------------------------------
-- Construction
-------------------------------------------------------------------------------

-- | Convert 'RE.RE' to 'DFA'.
--
-- >>> putPretty $ fromRE $ RE.star "abc"
-- 0+ -> \x -> if
--     | x <= '`'  -> 3
--     | x <= 'a'  -> 2
--     | otherwise -> 3
-- 1 -> \x -> if
--     | x <= 'b'  -> 3
--     | x <= 'c'  -> 0
--     | otherwise -> 3
-- 2 -> \x -> if
--     | x <= 'a'  -> 3
--     | x <= 'b'  -> 1
--     | otherwise -> 3
-- 3 -> \_ -> 3 -- black hole
--
-- Everything and nothing result in blackholes:
--
-- >>> traverse_ (putPretty . fromRE) [RE.empty, RE.star RE.anyChar]
-- 0 -> \_ -> 0 -- black hole
-- 0+ -> \_ -> 0 -- black hole
--
-- Character ranges are effecient:
--
-- >>> putPretty $ fromRE $ RE.charRange 'a' 'z'
-- 0 -> \x -> if
--     | x <= '`'  -> 2
--     | x <= 'z'  -> 1
--     | otherwise -> 2
-- 1+ -> \_ -> 2
-- 2 -> \_ -> 2 -- black hole
--
-- An example with two blackholes:
--
-- >>> putPretty $ fromRE $ "c" <> RE.star RE.anyChar
-- 0 -> \x -> if
--     | x <= 'b'  -> 2
--     | x <= 'c'  -> 1
--     | otherwise -> 2
-- 1+ -> \_ -> 1 -- black hole
-- 2 -> \_ -> 2 -- black hole
--
fromRE :: forall c. (Ord c, Enum c, Bounded c) => RE.RE c -> DFA Int c
fromRE = fromTM

-- | Convert 'ERE.ERE' to 'DFA'.
--
-- We don't always generate minimal automata:
--
-- >>> putPretty $ fromERE $ "a" /\ "b"
-- 0 -> \_ -> 1
-- 1 -> \_ -> 1 -- black hole
--
-- Compare this to an @complement@ example
--
-- Using 'fromTMEquiv', we can get minimal automaton, for the cost of higher
-- complexity (slow!).
--
-- >>> putPretty $ fromTMEquiv $ ("a" /\ "b" :: ERE.ERE Char)
-- 0 -> \_ -> 0 -- black hole
--
-- >>> putPretty $ fromERE $ complement $ star "abc"
-- 0 -> \x -> if
--     | x <= '`'  -> 3
--     | x <= 'a'  -> 2
--     | otherwise -> 3
-- 1+ -> \x -> if
--     | x <= 'b'  -> 3
--     | x <= 'c'  -> 0
--     | otherwise -> 3
-- 2+ -> \x -> if
--     | x <= 'a'  -> 3
--     | x <= 'b'  -> 1
--     | otherwise -> 3
-- 3+ -> \_ -> 3 -- black hole
--
fromERE :: forall c. (Ord c, Enum c, Bounded c) => ERE.ERE c -> DFA Int c
fromERE = fromTM

-- | Create from 'TransitionMap'.
--
-- See 'fromRE' for a specific example.
fromTM :: forall k c. (Ord k, Ord c, TransitionMap c k) => k -> DFA Int c
fromTM = fromTMImpl Nothing

-- | Create from 'TransitonMap' minimising states with 'Equivalent'.
--
-- See 'fromERE' for an example.
--
fromTMEquiv :: forall k c. (Ord k, Ord c, TransitionMap c k, Equivalent c k) => k -> DFA Int c
fromTMEquiv = fromTMImpl (Just equivalent)

fromTMImpl :: forall k c. (Ord k, Ord c, TransitionMap c k)
    => Maybe (k ->  k -> Bool)
    -> k
    -> DFA Int c
fromTMImpl mequiv re = DFA
    { dfaTransition = transition
    , dfaInitial    = 0
    , dfaAcceptable = Set.fromList
        [ i
        | (re', i) <- Map.toList lookupMap
        , nullable re'
        ]
    , dfaBlackholes = blackholes
    }
  where
    transition = Map.fromList
        [ (i, js)
        | (re', pm) <- Map.toList tm
        , let i  = fromMaybe 0 $ Map.lookup re' lookupMap
        , let js = SF.normalise $ fmap (\re'' -> fromMaybe 0 $ Map.lookup re'' lookupMap) pm
        ]

    blackholes = Set.fromList
        [ i
        | (i, sf) <- Map.toList transition
        , sf == pure i
        ]

    tm = transitionMap re

    -- reversing makes error state go last, usually
    lookupMap :: Map k Int
    lookupMap = makeLookup 1 lookupMap' (reverse $ Map.toList $ Map.delete re tm)

    lookupMap' :: Map k Int
    lookupMap' = case Map.lookup re tm of
        Nothing -> Map.empty
        Just _  -> Map.singleton re 0

    makeLookup :: Int -> Map k Int -> [(k, b)] -> Map k Int
    makeLookup = maybe makeLookupEq makeLookupEquiv mequiv

    makeLookupEq :: Int -> Map k Int -> [(k, b)] -> Map k Int
    makeLookupEq !_ !acc []            = acc
    makeLookupEq !n acc ((x, _) : xs) = makeLookup (n + 1) (Map.insert x n acc) xs

    -- this differs from makeLookupEq. We don't insert new states right away,
    -- but check whether equivalent state is already in the map.
    --
    -- This causes n^2 of exp m operations, where n = number of states and
    -- m size of @k@.
    makeLookupEquiv :: (k -> k -> Bool) ->  Int -> Map k Int -> [(k, b)] -> Map k Int
    makeLookupEquiv _  !_ !acc []           = acc
    makeLookupEquiv eq !n acc ((x, _) : xs) = case ys of
        []           -> makeLookup (n + 1) (Map.insert x n acc) xs
        ((_, i) : _) -> makeLookup n       (Map.insert x i acc) xs
      where
        ys = [ p | p@(y, _) <- Map.toList acc, eq x y ]

-------------------------------------------------------------------------------
-- Destruction
-------------------------------------------------------------------------------

-- | Convert 'DFA' to 'RE.RE'.
--
-- >>> putPretty $ toRE $ fromRE "foobar"
-- ^foobar$
--
-- For 'RE.string' regular expressions, @'toRE' . 'fromRE' = 'id'@:
--
-- prop> let s = take 5 s' in RE.string (s :: String) === toRE (fromRE (RE.string s))
--
-- But in general it isn't:
--
-- >>> let aToZ = RE.star $ RE.charRange 'a' 'z'
-- >>> traverse_ putPretty [aToZ, toRE $ fromRE aToZ]
-- ^[a-z]*$
-- ^([a-z]|[a-z]?[a-z]*[a-z]?)?$
--
-- @
-- not-prop> (re :: RE.RE Char) === toRE (fromRE re)
-- @
--
-- However, they are 'RE.equivalent':
--
-- >>> RE.equivalent aToZ (toRE (fromRE aToZ))
-- True
--
-- And so are others
--
-- >>> all (\re -> RE.equivalent re (toRE (fromRE re))) [RE.star "a", RE.star "ab"]
-- True
--
-- @
-- expensive-prop> RE.equivalent re (toRE (fromRE (re :: RE.RE Char)))
-- @
--
-- Note, that @'toRE' . 'fromRE'@ can, and usually makes regexp unrecognisable:
--
-- >>> putPretty $ toRE $ fromRE $ RE.star "ab"
-- ^(a(ba)*b)?$
--
-- We can 'complement' DFA, therefore we can complement 'RE.RE'.
-- For example. regular expression matching string containing an @a@:
--
-- >>> let withA = RE.star RE.anyChar <> "a" <> RE.star RE.anyChar
-- >>> let withoutA = toRE $ complement $ fromRE withA
-- >>> putPretty withoutA
-- ^([^a]|[^a]?[^a]*[^a]?)?$
--
-- >>> let withoutA' = RE.star $ RE.REChars $ RSet.complement $ RSet.singleton 'a'
-- >>> putPretty withoutA'
-- ^[^a]*$
--
-- >>> RE.equivalent withoutA withoutA'
-- True
--
-- Quite small, for example 2 state DFAs can result in big regular expressions:
--
-- >>> putPretty $ toRE $ complement $ fromRE $ star "ab"
-- ^([^]|a(ba)*(ba)?|a(ba)*([^b]|b[^a])|([^a]|a(ba)*([^b]|b[^a]))[^]*[^]?)$
--
-- We can use @'toRE' . 'fromERE'@ to convert 'ERE.ERE' to 'RE.RE':
--
-- >>> putPretty $ toRE $ fromERE $ complement $ star "ab"
-- ^([^]|a(ba)*(ba)?|a(ba)*([^b]|b[^a])|([^a]|a(ba)*([^b]|b[^a]))[^]*[^]?)$
--
-- >>> putPretty $ toRE $ fromERE $ "a" /\ "b"
-- ^[]$
--
-- See <https://mathoverflow.net/questions/45149/can-regular-expressions-be-made-unambiguous>
-- for the description of the algorithm used.
--
toRE :: (Ord c, Enum c, Bounded c) => DFA Int c -> RE.RE c
toRE = toKleene

-- | Convert 'DFA' to 'ERE.ERE'.
toERE :: (Ord c, Enum c, Bounded c) => DFA Int c -> ERE.ERE c
toERE = toKleene

-- | Convert to any 'Kleene'.
--
-- See 'toRE' for a specific example.
--
toKleene :: forall k c. (Ord c, Enum c, Bounded c, FiniteKleene c k) => DFA Int c -> k
toKleene (DFA tr ini acc _) = unions
    [ re ini j maxN
    | j <- Set.toList acc
    ]
  where
    maxN | Map.null tr = 1
         | otherwise = succ $ fst $ Map.findMax tr

    {-
    -- this is useful for debug
    table =
      [ show i ++ " " ++ show j ++ " " ++ show k ++ " = " ++ pretty (re i j k)
      | k <- [0..pred maxN]
      , i <- [0..pred maxN]
      , j <- [0..pred maxN]
      ]
    -}

    re i j k = MT.memo re' (i, j, k)
    re' (i, j, k)
        | k <= 0    = if i == j then eps \/ r else r
        | otherwise = re i j k' \/ (re i k' k' <> star (re k' k' k') <> re k' j k')
      where
        r = maybe empty fromRSet $ Map.lookup (i, j) re0map
        k' = k - 1

    re0map :: Map (Int, Int) (RSet c)
    re0map = Map.fromListWith RSet.union
        [ ((i, j), RSet.singletonRange (lo, hi))
        | (i, tr') <- Map.toList tr
        , (lo, hi, j) <- toPieces tr'
        ]

toPieces :: (Enum a, Bounded a, Ord a) => SF.SF a b -> [(a, a, b)]
toPieces (SF.SF m v)
    | maxBound `Map.member` m = toPieces' m
    | otherwise               = toPieces' (Map.insert maxBound v m)

toPieces' :: (Enum a, Bounded a) => Map a b -> [(a, a, b)]
toPieces' = go minBound . Map.toList where
    go _lo []            = []
    go  lo ((k, v) : kv) = (lo, k, v) : go (succ k) kv

-------------------------------------------------------------------------------
-- Operations
-------------------------------------------------------------------------------

-- | Run 'DFA' on the input.
--
-- Because we have analysed a language, in some cases we can determine an input
-- without traversing all of the input.
-- That's not the cases with 'RE.RE' 'match'.
--
-- >>> let dfa = fromRE $ RE.star "abc"
-- >>> map (match dfa) ["", "abc", "abcabc", "aa", 'a' : 'a' : undefined]
-- [True,True,True,False,False]
--
-- Holds:
--
-- @
-- 'match' ('fromRE' re) xs == 'match' re xs
-- @
--
-- prop> all (match (fromRE r)) $ take 10 $ RE.generate (curry QC.choose) 42 (r :: RE.RE Char)
--
instance (Ord s, Ord c) => Match c (DFA s c) where
    match (DFA tr i acc bh) = go i where
        go !s _ | Set.member s bh = Set.member s acc
        go !s []                 = Set.member s acc
        go !s (c : cs)           = case Map.lookup s tr of
            Nothing -> False
            Just sf -> go (sf SF.! c) cs

    match8 (DFA tr i acc bh) = go i where
        go !s !_ | Set.member s bh = Set.member s acc
        go !s bs = case BS.uncons bs of
            Nothing      -> Set.member s acc
            Just (c, cs) -> case Map.lookup s tr of
                Nothing -> False
                Just sf -> go (sf SF.! c) cs

-- | Complement DFA.
--
-- Complement of 'DFA' is way easier than of 'RE.RE': complement accept states.
--
-- >>> let dfa = complement $ fromRE $ RE.star "abc"
-- >>> putPretty dfa
-- 0 -> \x -> if
--     | x <= '`'  -> 3
--     | x <= 'a'  -> 2
--     | otherwise -> 3
-- 1+ -> \x -> if
--     | x <= 'b'  -> 3
--     | x <= 'c'  -> 0
--     | otherwise -> 3
-- 2+ -> \x -> if
--     | x <= 'a'  -> 3
--     | x <= 'b'  -> 1
--     | otherwise -> 3
-- 3+ -> \_ -> 3 -- black hole
--
-- >>> map (match dfa) ["", "abc", "abcabc", "aa","abca", 'a' : 'a' : undefined]
-- [False,False,False,True,True,True]
--
instance Ord s => Complement c (DFA s c) where
    complement (DFA tr ini acc bh) = DFA tr ini acc' bh where
        acc' = Set.difference (Map.keysSet tr) acc

instance (Ord s, Ord c) => Derivate c (DFA s c) where
    nullable (DFA _tr ini acc _bh) = Set.member ini acc

    derivate c (DFA tr ini acc bh) = DFA tr ini' acc bh where
        ini' = case Map.lookup ini tr of
            Nothing -> ini -- in error case let's just stay in the same state.
            Just sf -> sf SF.! c

-------------------------------------------------------------------------------
-- toDot
-------------------------------------------------------------------------------

-- | Get Graphviz dot-code of DFA.
--
-- >>> let dfa = fromRE $ RE.star "abc"
-- >>> putStr $ toDot dfa
-- digraph dfa {
-- rankdir=LR;
-- // states
-- "0" [shape=doublecircle];
-- "1" [shape=circle];
-- "2" [shape=circle];
-- // initial state
-- "" [shape=none];
-- "" -> "0";
-- // transitions
-- "0" -> "2"[label="a"]
-- "1" -> "0"[label="c"]
-- "2" -> "1"[label="b"]
-- }
--
toDot :: DFA Int Char -> String
toDot = toDot' show pure

-- | More flexible version of 'toDot'.
toDot' :: (Ord s, Ord c, Enum c, Bounded c) => (s -> String) -> (c -> String) -> DFA s c -> String
toDot' showS showC (DFA tr ini acc bh)
    = showString "digraph dfa {\n"
    . showString "rankdir=LR;\n"
    . showString "// states\n"
    . showStates
    . showString "// initial state\n"
    . showInitial
    . showString "// transitions\n"
    . showTransitions
    . showString "}\n"
    $ ""
  where
    showStates  = foldr (.) id
        [ showState i
        | i <- Map.keys tr
        , Set.member i acc || Set.notMember i bh
        ]
    showState s = showS' s . shape where
        shape
            | Set.member s acc = showString " [shape=doublecircle];\n"
            | otherwise        = showString " [shape=circle];\n"

    showInitial
        = showString "\"\" [shape=none];\n"
        . showString "\"\" -> "
        . showS' ini
        . showString ";\n"

    showTransitions = foldr (.) id
        [ showS' i
        . showString " -> "
        . showS' j
        . showString "[label="
        . label
                . showString "]\n"
        | (i, sf) <- Map.toList tr
        , (lo, hi, j) <- toPieces sf
        , Set.member j acc || Set.notMember j bh
        , let label
                | lo == hi
                    = shows (showC lo)
                | lo == minBound && hi == maxBound
                    = shows ("-any" :: String)
                | otherwise
                    = shows (showC lo ++ "-" ++ showC hi)
        ]

    showS' = shows . showS

-------------------------------------------------------------------------------
-- Debug
-------------------------------------------------------------------------------

instance (Show s, Show c, Ord s) => Pretty (DFA s c) where
    pretty dfa = intercalate "\n"
        [ show i ++ acc ++ " -> " ++ SF.showSF sf ++ bh
        | (i, sf) <- Map.toList (dfaTransition dfa)
        , let acc = if Set.member i (dfaAcceptable dfa) then "+" else ""
        , let bh = if Set.member i $ dfaBlackholes dfa then " -- black hole" else ""
        ]

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Data.Foldable (traverse_)
-- >>> import Algebra.Lattice ((/\))
--
-- >>> import Test.QuickCheck ((===))
-- >>> import qualified Test.QuickCheck as QC
--
-- >>> newtype Smaller a = Smaller a deriving (Show)
-- >>> let intLog2 = (`div` 10)
-- >>> instance QC.Arbitrary a => QC.Arbitrary (Smaller a) where arbitrary = QC.scale intLog2 QC.arbitrary; shrink (Smaller a) = map Smaller (QC.shrink a)

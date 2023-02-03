{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Safe                  #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Kleene.ERE (
    ERE (..),
    -- * Construction
    --
    -- | Binary operators are
    --
    -- * '<>' for append
    -- * '\/' for union
    -- * '/\' for intersection
    --
    empty,
    eps,
    everything,
    char,
    charRange,
    anyChar,
    appends,
    unions,
    intersections,
    star,
    string,
    complement,
    -- * Derivative
    nullable,
    derivate,
    -- * Conversion
    fromRE,
    -- * Transition map
    transitionMap,
    leadingChars,
    -- * Equivalence
    equivalent,
    -- * Other
    isEmpty,
    isEverything,
    ) where

import Data.Semigroup (Semigroup (..))
import Prelude ()
import Prelude.Compat

import Algebra.Lattice
       (BoundedJoinSemiLattice (..), BoundedMeetSemiLattice (..), Lattice (..))
import Control.Applicative (liftA2)
import Data.Foldable       (toList)
import Data.List           (foldl')
import Data.Map            (Map)
import Data.RangeSet.Map   (RSet)
import Data.Set            (Set)
import Data.String         (IsString (..))

import qualified Data.Function.Step.Discrete.Closed as SF
import qualified Data.Map                           as Map
import qualified Data.RangeSet.Map                  as RSet
import qualified Data.Set                           as Set
import qualified Test.QuickCheck                    as QC

import qualified Kleene.Classes            as C
import qualified Kleene.Internal.Partition as P
import           Kleene.Internal.Pretty
import qualified Kleene.Internal.RE        as RE

-- $setup
-- >>> import Algebra.Lattice ((/\), (\/), top, bottom)
-- >>> import Data.Semigroup (Semigroup (..))
-- >>> import Control.Monad (void)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.List (sort)
-- >>> import Test.QuickCheck ((===))
-- >>> import qualified Test.QuickCheck as QC
-- >>> import qualified Data.Map as Map
-- >>> import qualified Data.Function.Step.Discrete.Closed as SF
--
-- >>> import Kleene.Classes (match)
-- >>> import Kleene.Internal.Pretty (putPretty, pretty)
-- >>> let asEREChar :: ERE Char -> ERE Char; asEREChar = id

-- | Extended regular expression
--
-- It's both, /Kleene/ and /Boolean/ algebra. (If we add only intersections, it
-- wouldn't be /Boolean/).
--
-- /Note:/ we don't have special constructor for intersections.
-- We use de Morgan formula \(a \land b = \neg (\neg a \lor \neg b)\).
--
-- >>> putPretty $ asEREChar $ "a" /\ "b"
-- ^~(~a|~b)$
--
-- There is no generator, as 'intersections' makes it hard.
--
data ERE c
    = EREChars (RSet c)                -- ^ Single character
    | EREAppend [ERE c]                -- ^ Concatenation
    | EREUnion (RSet c) (Set (ERE c))  -- ^ Union
    | EREStar (ERE c)                  -- ^ Kleene star
    | ERENot (ERE c)                   -- ^ Complement
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- fromRE
-------------------------------------------------------------------------------

-- | Convert from ordinary regular expression, 'RE.RE'.
--
fromRE :: Ord c => RE.RE c -> ERE c
fromRE (RE.REChars rs)   = EREChars rs
fromRE (RE.REAppend rs)  = EREAppend (map fromRE rs)
fromRE (RE.REUnion r rs) = EREUnion r (Set.map fromRE rs)
fromRE (RE.REStar r)     = EREStar (fromRE r)

-------------------------------------------------------------------------------
-- Smart constructor
-------------------------------------------------------------------------------

-- | Empty regex. Doesn't accept anything.
--
-- >>> putPretty (empty :: ERE Char)
-- ^[]$
--
-- >>> putPretty (bottom :: ERE Char)
-- ^[]$
--
-- prop> match (empty :: ERE Char) (s :: String) === False
--
empty :: ERE c
empty = EREChars RSet.empty

-- | Everything.
--
-- >>> putPretty (everything :: ERE Char)
-- ^~[]$
--
-- >>> putPretty (top :: ERE Char)
-- ^~[]$
--
-- prop> match (everything :: ERE Char) (s :: String) === True
--
everything :: ERE c
everything = complement empty

-- | Empty string. /Note:/ different than 'empty'.
--
-- >>> putPretty eps
-- ^$
--
-- >>> putPretty (mempty :: ERE Char)
-- ^$
--
-- prop> match (eps :: ERE Char) s === null (s :: String)
--
eps :: ERE c
eps = EREAppend []

-- |
--
-- >>> putPretty (char 'x')
-- ^x$
--
char :: c -> ERE c
char = EREChars . RSet.singleton

-- |
--
-- >>> putPretty $ charRange 'a' 'z'
-- ^[a-z]$
--
charRange :: Ord c => c -> c -> ERE c
charRange c c' = EREChars $ RSet.singletonRange (c, c')

-- | Any character. /Note:/ different than dot!
--
-- >>> putPretty anyChar
-- ^[^]$
--
anyChar :: Bounded c => ERE c
anyChar = EREChars RSet.full

-- | Concatenate regular expressions.
--
-- prop> asEREChar r <> empty === empty
-- prop> empty <> asEREChar r === empty
-- prop> (asEREChar r <> s) <> t === r <> (s <> t)
--
-- prop> asEREChar r <> eps === r
-- prop> eps <> asEREChar r === r
--
appends :: Eq c => [ERE c] -> ERE c
appends rs0
    | elem empty rs1 = empty
    | otherwise = case rs1 of
        [r] -> r
        rs  -> EREAppend rs
  where
    -- flatten one level of EREAppend
    rs1 = concatMap f rs0

    f (EREAppend rs) = rs
    f r              = [r]

-- | Union of regular expressions.
--
-- prop> asEREChar r \/ r === r
-- prop> asEREChar r \/ s === s \/ r
-- prop> (asEREChar r \/ s) \/ t === r \/ (s \/ t)
--
-- prop> empty \/ asEREChar r === r
-- prop> asEREChar r \/ empty === r
--
-- prop> everything \/ asEREChar r === everything
-- prop> asEREChar r \/ everything === everything
--
unions :: (Ord c, Enum c) => [ERE c] -> ERE c
unions = uncurry mk . foldMap f where
    mk cs rss
        | Set.null rss = EREChars cs
        | Set.member everything rss = everything
        | RSet.null cs = case Set.toList rss of
            []  -> empty
            [r] -> r
            _   -> EREUnion cs rss
        | otherwise    = EREUnion cs rss

    f (EREUnion cs rs) = (cs, rs)
    f (EREChars cs)    = (cs, Set.empty)
    f r                = (mempty, Set.singleton r)

-- | Intersection of regular expressions.
--
-- prop> asEREChar r /\ r === r
-- prop> asEREChar r /\ s === s /\ r
-- prop> (asEREChar r /\ s) /\ t === r /\ (s /\ t)
--
-- prop> empty /\ asEREChar r === empty
-- prop> asEREChar r /\ empty === empty
--
-- prop> everything /\ asEREChar r === r
-- prop> asEREChar r /\ everything === r
--
intersections :: (Ord c, Enum c) => [ERE c] -> ERE c
intersections = complement . unions . map complement

-- | Complement.
--
-- prop> complement (complement r) === asEREChar r
--
complement :: ERE c -> ERE c
complement r = case r of
    ERENot r' -> r'
    _ -> ERENot r

-- | Kleene star.
--
-- prop> star (star r) === star (asEREChar r)
--
-- prop> star eps     === asEREChar eps
-- prop> star empty   === asEREChar eps
-- prop> star anyChar === asEREChar everything
--
-- prop> star (asEREChar r \/ eps) === star r
-- prop> star (char c \/ eps) === star (char (c :: Char))
-- prop> star (empty \/ eps) === eps
--
star :: (Ord c, Bounded c) => ERE c -> ERE c
star r = case r of
    EREStar _                          -> r
    EREAppend []                       -> eps
    EREChars cs | RSet.null cs         -> eps
    EREChars cs | RSet.isFull cs       -> everything
    EREUnion cs rs | Set.member eps rs -> case Set.toList rs' of
        []                  -> star (EREChars cs)
        [r'] | RSet.null cs -> star r'
        _                   -> EREStar (EREUnion cs rs')
      where
        rs' = Set.delete eps rs
    _                                  -> EREStar r

-- | Literal string.
--
-- >>> putPretty ("foobar" :: ERE Char)
-- ^foobar$
--
-- >>> putPretty ("(.)" :: ERE Char)
-- ^\(\.\)$
--
string :: [c] -> ERE c
string []  = eps
string [c] = EREChars (RSet.singleton c)
string cs  = EREAppend $ map (EREChars . RSet.singleton) cs

instance (Ord c, Enum c, Bounded c) => C.Kleene (ERE c) where
    empty      = empty
    eps        = eps
    appends    = appends
    unions     = unions
    star       = star

instance (Ord c, Enum c, Bounded c) => C.CharKleene c (ERE c) where
    char       = char

instance (Ord c, Enum c, Bounded c) => C.FiniteKleene c (ERE c) where
    everything = everything
    charRange  = charRange
    fromRSet   = EREChars
    anyChar    = anyChar

instance C.Complement c (ERE c) where
    complement = complement

-------------------------------------------------------------------------------
-- derivative
-------------------------------------------------------------------------------

-- | We say that a regular expression r is nullable if the language it defines
-- contains the empty string.
--
-- >>> nullable eps
-- True
--
-- >>> nullable (star "x")
-- True
--
-- >>> nullable "foo"
-- False
--
-- >>> nullable (complement eps)
-- False
--
nullable :: ERE c -> Bool
nullable (EREChars _)      = False
nullable (EREAppend rs)    = all nullable rs
nullable (EREUnion _cs rs) = any nullable rs
nullable (EREStar _)       = True
nullable (ERENot r)        = not (nullable r)

-- | Intuitively, the derivative of a language \(\mathcal{L} \subset \Sigma^\star\)
-- with respect to a symbol \(a \in \Sigma\) is the language that includes only
-- those suffixes of strings with a leading symbol \(a\) in \(\mathcal{L}\).
--
-- >>> putPretty $ derivate 'f' "foobar"
-- ^oobar$
--
-- >>> putPretty $ derivate 'x' $ "xyz" \/ "abc"
-- ^yz$
--
-- >>> putPretty $ derivate 'x' $ star "xyz"
-- ^yz(xyz)*$
--
derivate :: (Ord c, Enum c) => c -> ERE c -> ERE c
derivate c (EREChars cs)     = derivateChars c cs
derivate c (EREUnion cs rs)  = unions $ derivateChars c cs : [ derivate c r | r <- toList rs]
derivate c (EREAppend rs)    = derivateAppend c rs
derivate c rs@(EREStar r)    = derivate c r <> rs
derivate c (ERENot r)        = complement (derivate c r)

instance (Ord c, Enum c) => C.Derivate c (ERE c) where
    nullable = nullable
    derivate = derivate

instance (Ord c, Enum c) => C.Match c (ERE c) where
    match r = nullable . foldl' (flip derivate) r

derivateAppend :: (Enum c, Ord c) => c -> [ERE c] -> ERE c
derivateAppend _ []      = empty
derivateAppend c [r]     = derivate c r
derivateAppend c (r:rs)
    | nullable r         = unions [r' <> appends rs, rs']
    | otherwise          = r' <> appends rs
  where
    r'  = derivate c r
    rs' = derivateAppend c rs

derivateChars :: Ord c =>  c -> RSet c -> ERE c
derivateChars c cs
    | c `RSet.member` cs      = eps
    | otherwise               = empty

-------------------------------------------------------------------------------
-- isEmpty
-------------------------------------------------------------------------------

-- | Whether 'ERE' is (structurally) equal to 'empty'.
isEmpty :: ERE c -> Bool
isEmpty (EREChars rs) = RSet.null rs
isEmpty _            = False

-- | Whether 'ERE' is (structurally) equal to 'everything'.
isEverything :: ERE c -> Bool
isEverything (ERENot (EREChars rs)) = RSet.null rs
isEverything _                      = False

-------------------------------------------------------------------------------
-- States
-------------------------------------------------------------------------------

-- | Transition map. Used to construct 'Kleene.DFA.DFA'.
--
-- >>> void $ Map.traverseWithKey (\k v -> putStrLn $ pretty k ++ " : " ++ SF.showSF (fmap pretty v)) $ transitionMap ("ab" :: ERE Char)
-- ^[]$ : \_ -> "^[]$"
-- ^b$ : \x -> if
--     | x <= 'a'  -> "^[]$"
--     | x <= 'b'  -> "^$"
--     | otherwise -> "^[]$"
-- ^$ : \_ -> "^[]$"
-- ^ab$ : \x -> if
--     | x <= '`'  -> "^[]$"
--     | x <= 'a'  -> "^b$"
--     | otherwise -> "^[]$"
--
transitionMap
    :: forall c. (Ord c, Enum c, Bounded c)
    => ERE c
    -> Map (ERE c) (SF.SF c (ERE c))
transitionMap re = go Map.empty [re] where
    go :: Map (ERE c) (SF.SF c (ERE c))
       -> [ERE c]
       -> Map (ERE c) (SF.SF c (ERE c))
    go !acc [] = acc
    go acc (r : rs)
        | r `Map.member` acc = go acc rs
        | otherwise = go (Map.insert r pm acc) (SF.values pm ++ rs)
      where
        pm = P.toSF (\c -> derivate c r) (leadingChars r)

instance (Ord c, Enum c, Bounded c) => C.TransitionMap c (ERE c) where
    transitionMap = transitionMap

-- | Leading character sets of regular expression.
--
-- >>> leadingChars "foo"
-- fromSeparators "ef"
--
-- >>> leadingChars (star "b" <> star "e")
-- fromSeparators "abde"
--
-- >>> leadingChars (charRange 'b' 'z')
-- fromSeparators "az"
--
leadingChars :: (Ord c, Enum c, Bounded c) => ERE c -> P.Partition c
leadingChars (EREChars cs)    = P.fromRSet cs
leadingChars (EREUnion cs rs) = P.fromRSet cs <> foldMap leadingChars rs
leadingChars (EREStar r)      = leadingChars r
leadingChars (EREAppend rs)   = leadingCharsAppend rs
leadingChars (ERENot r)       = leadingChars r

leadingCharsAppend :: (Ord c, Enum c, Bounded c) => [ERE c] -> P.Partition c
leadingCharsAppend [] = P.whole
leadingCharsAppend (r : rs)
    | nullable r = leadingChars r <> leadingCharsAppend rs
    | otherwise  = leadingChars r

-------------------------------------------------------------------------------
-- Equivalence
-------------------------------------------------------------------------------

-- | Whether two regexps are equivalent.
--
-- @
-- 'equivalent' re1 re2 <=> forall s. 'match' re1 s == 'match' re1 s
-- @
--
-- >>> let re1 = star "a" <> "a"
-- >>> let re2 = "a" <> star "a"
--
-- These are different regular expressions, even we perform
-- some normalisation-on-construction:
--
-- >>> re1 == re2
-- False
--
-- They are however equivalent:
--
-- >>> equivalent re1 re2
-- True
--
-- The algorithm works by executing 'states' on "product" regexp,
-- and checking whether all resulting states are both accepting or rejecting.
--
-- @
-- re1 == re2 ==> 'equivalent' re1 re2
-- @
--
-- === More examples
--
-- >>> let example re1 re2 = putPretty re1 >> putPretty re2 >> return (equivalent re1 re2)
-- >>> example re1 re2
-- ^a*a$
-- ^aa*$
-- True
--
-- >>> example (star "aa") (star "aaa")
-- ^(aa)*$
-- ^(aaa)*$
-- False
--
-- >>> example (star "aa" <> star "aaa") (star "aaa" <> star "aa")
-- ^(aa)*(aaa)*$
-- ^(aaa)*(aa)*$
-- True
--
-- >>> example (star ("a" \/ "b")) (star $ star "a" <> star "b")
-- ^[a-b]*$
-- ^(a*b*)*$
-- True
--
equivalent :: forall c. (Ord c, Enum c, Bounded c) => ERE c -> ERE c -> Bool
equivalent x0 y0 = go mempty [(x0, y0)] where
    go :: Set (ERE c, ERE c) -> [(ERE c, ERE c)] -> Bool
    go !_ [] = True
    go acc (p@(x, y) : zs)
        | p `Set.member` acc = go acc zs
        -- if two regexps are structurally the same, we don't need to recurse.
        | x == y             = go (Set.insert p acc) zs
        | all agree ps       = go (Set.insert p acc) (ps ++ zs)
        | otherwise = False
      where
        cs = toList $ P.examples $ leadingChars x `P.wedge` leadingChars y
        ps = map (\c -> (derivate c x, derivate c y)) cs

    agree :: (ERE c, ERE c) -> Bool
    agree (x, y) = nullable x == nullable y

instance (Ord c, Enum c, Bounded c) => C.Equivalent c (ERE c) where
    equivalent = equivalent

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Eq c => Semigroup (ERE c) where
    r <> r' = appends [r, r']

instance Eq c => Monoid (ERE c) where
    mempty  = eps
    mappend = (<>)
    mconcat = appends

instance (Ord c, Enum c) => Lattice (ERE c) where
    r \/ r' = unions [r, r']
    r /\ r' = intersections [r, r']

instance (Ord c, Enum c) => BoundedJoinSemiLattice (ERE c) where
    bottom = empty

instance (Ord c, Enum c) => BoundedMeetSemiLattice (ERE c) where
    top = everything

instance c ~ Char => IsString (ERE c) where
    fromString = string

instance (Ord c, Enum c, Bounded c, QC.Arbitrary c) => QC.Arbitrary (ERE c) where
    arbitrary = QC.sized arb where
        c :: QC.Gen (ERE c)
        c = EREChars . RSet.fromRangeList <$> QC.arbitrary

        arb :: Int -> QC.Gen (ERE c)
        arb n | n <= 0    = QC.oneof [c, fmap char QC.arbitrary, pure eps]
              | otherwise = QC.oneof
            [ c
            , pure eps
            , fmap char QC.arbitrary
            , liftA2 (<>) (arb n2) (arb n2)
            , liftA2 (\/) (arb n2) (arb n2)
            , fmap star (arb n2)
            , fmap complement (arb n2)
            ]
          where
            n2 = n `div` 2

instance (QC.CoArbitrary c) => QC.CoArbitrary (ERE c) where
    coarbitrary (EREChars cs)    = QC.variant (0 :: Int) . QC.coarbitrary (RSet.toRangeList cs)
    coarbitrary (EREAppend rs)   = QC.variant (1 :: Int) . QC.coarbitrary rs
    coarbitrary (EREUnion cs rs) = QC.variant (2 :: Int) . QC.coarbitrary (RSet.toRangeList cs, Set.toList rs)
    coarbitrary (EREStar r)      = QC.variant (3 :: Int) . QC.coarbitrary r
    coarbitrary (ERENot r)       = QC.variant (4 :: Int) . QC.coarbitrary r

-------------------------------------------------------------------------------
-- JavaScript
-------------------------------------------------------------------------------

instance c ~ Char => Pretty (ERE c) where
    prettyS x = showChar '^' . go False x . showChar '$'
      where
        go :: Bool -> ERE Char -> ShowS
        go p (EREStar a)
            = parens p
            $ go True a . showChar '*'
        go p (EREAppend rs)
            = parens p $ goMany id rs
        go p (EREUnion cs rs)
            | RSet.null cs = goUnion p rs
            | Set.null rs  = prettyS cs
            | otherwise    = goUnion p (Set.insert (EREChars cs) rs)
        go _ (EREChars cs)
            = prettyS cs
        go p (ERENot r)
            = parens p $ showChar '~' . go True r

        goUnion p rs
            | Set.member eps rs = parens p $ goUnion' True . showChar '?'
            | otherwise         = goUnion' p
          where
            goUnion' p' = case Set.toList (Set.delete eps rs) of
                [] -> go True empty
                [r] -> go p' r
                (r:rs') -> parens True $ goSome1 (showChar '|') r rs'

        goMany :: ShowS -> [ERE Char] -> ShowS
        goMany sep = foldr (\a b -> go False a . sep . b) id

        goSome1 :: ShowS -> ERE Char -> [ERE Char] -> ShowS
        goSome1 sep r = foldl (\a b -> a . sep . go False b) (go False r)

        parens :: Bool -> ShowS -> ShowS
        parens True  s = showString "(" . s . showChar ')'
        parens False s = s

-------------------------------------------------------------------------------
-- Latin1
-------------------------------------------------------------------------------

instance C.ToLatin1 ERE where
    toLatin1 (EREChars rs)    = C.fromRSet (C.toLatin1 rs)
    toLatin1 (EREAppend xs)   = appends (map C.toLatin1 xs)
    toLatin1 (EREUnion rs xs) = C.fromRSet (C.toLatin1 rs) \/ unions (map C.toLatin1 (Set.toList  xs))
    toLatin1 (EREStar r)      = star (C.toLatin1 r)
    toLatin1 (ERENot r)       = complement (C.toLatin1 r)

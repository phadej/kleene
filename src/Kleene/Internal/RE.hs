{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Kleene.Internal.RE (
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

import Prelude ()
import Prelude.Compat
import Data.Semigroup (Semigroup (..))

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
import qualified Test.QuickCheck.Gen                as QC (unGen)
import qualified Test.QuickCheck.Random             as QC (mkQCGen)

import qualified Kleene.Classes            as C
import qualified Kleene.Internal.Partition as P
import           Kleene.Internal.Pretty

-- | Regular expression
--
-- Constructors are exposed, but you should use
-- smart constructors in this module to construct 'RE'.
--
-- The 'Eq' and 'Ord' instances are structural.
-- The 'Kleene' etc constructors do "weak normalisation", so for values
-- constructed using those operations 'Eq' witnesses "weak equivalence".
-- See 'equivalent' for regular-expression equivalence.
--
-- Structure is exposed in "Kleene.RE" module but consider constructors as
-- half-internal.  There are soft-invariants, but violating them shouldn't
-- break anything in the package. (e.g. 'transitionMap' will eventually
-- terminate, but may create more redundant states if starting regexp is not
-- "weakly normalised").
--
data RE c
    = REChars (RSet c)               -- ^ Single character
    | REAppend [RE c]                -- ^ Concatenation
    | REUnion (RSet c) (Set (RE c))  -- ^ Union
    | REStar (RE c)                  -- ^ Kleene star
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Smart constructor
-------------------------------------------------------------------------------

-- | Empty regex. Doesn't accept anything.
--
-- >>> putPretty (empty :: RE Char)
-- ^[]$
--
-- >>> putPretty (bottom :: RE Char)
-- ^[]$
--
-- prop> match (empty :: RE Char) (s :: String) === False
--
empty :: RE c
empty = REChars RSet.empty

-- | Everything.
--
-- >>> putPretty everything
-- ^[^]*$
--
-- prop> match (everything :: RE Char) (s :: String) === True
--
everything :: Bounded c => RE c
everything = REStar (REChars RSet.full)

-- | Empty string. /Note:/ different than 'empty'.
--
-- >>> putPretty eps
-- ^$
--
-- >>> putPretty (mempty :: RE Char)
-- ^$
--
-- prop> match (eps :: RE Char) s === null (s :: String)
--
eps :: RE c
eps = REAppend []

-- |
--
-- >>> putPretty (char 'x')
-- ^x$
--
char :: c -> RE c
char = REChars . RSet.singleton

-- |
--
-- >>> putPretty $ charRange 'a' 'z'
-- ^[a-z]$
--
charRange :: Ord c => c -> c -> RE c
charRange c c' = REChars $ RSet.singletonRange (c, c')

-- | Any character. /Note:/ different than dot!
--
-- >>> putPretty anyChar
-- ^[^]$
--
anyChar :: Bounded c => RE c
anyChar = REChars RSet.full

-- | Concatenate regular expressions.
--
-- prop> (asREChar r <> s) <> t === r <> (s <> t)
--
-- prop> asREChar r <> empty === empty
-- prop> empty <> asREChar r === empty
--
-- prop> asREChar r <> eps === r
-- prop> eps <> asREChar r === r
--
appends :: Eq c => [RE c] -> RE c
appends rs0
    | elem empty rs1 = empty
    | otherwise = case rs1 of
        [r] -> r
        rs  -> REAppend rs
  where
    -- flatten one level of REAppend
    rs1 = concatMap f rs0

    f (REAppend rs) = rs
    f r             = [r]

-- | Union of regular expressions.
--
-- prop> asREChar r \/ r === r
-- prop> asREChar r \/ s === s \/ r
-- prop> (asREChar r \/ s) \/ t === r \/ (s \/ t)
--
-- prop> empty \/ asREChar r === r
-- prop> asREChar r \/ empty === r
--
-- prop> everything \/ asREChar r === everything
-- prop> asREChar r \/ everything === everything
--
unions :: (Ord c, Enum c, Bounded c) => [RE c] -> RE c
unions = uncurry mk . foldMap f where
    mk cs rss
        | Set.null rss = REChars cs
        | Set.member everything rss = everything
        | RSet.null cs = case Set.toList rss of
            []  -> empty
            [r] -> r
            _   -> REUnion cs rss
        | otherwise    = REUnion cs rss

    f (REUnion cs rs) = (cs, rs)
    f (REChars cs)    = (cs, Set.empty)
    f r               = (mempty, Set.singleton r)

-- | Kleene star.
--
-- prop> star (star r) === star (asREChar r)
--
-- prop> star eps     === asREChar eps
-- prop> star empty   === asREChar eps
-- prop> star anyChar === asREChar everything
--
-- prop> star (r      \/ eps) === star (asREChar r)
-- prop> star (char c \/ eps) === star (asREChar (char c))
-- prop> star (empty  \/ eps) === asREChar eps
--
star :: Ord c => RE c -> RE c
star r = case r of
    REStar _                          -> r
    REAppend []                       -> eps
    REChars cs | RSet.null cs         -> eps
    REUnion cs rs | Set.member eps rs -> case Set.toList rs' of
        []                  -> star (REChars cs)
        [r'] | RSet.null cs -> star r'
        _                   -> REStar (REUnion cs rs')
      where
        rs' = Set.delete eps rs
    _                                 -> REStar r

-- | Literal string.
--
-- >>> putPretty ("foobar" :: RE Char)
-- ^foobar$
--
-- >>> putPretty ("(.)" :: RE Char)
-- ^\(\.\)$
--
string :: [c] -> RE c
string []  = eps
string [c] = REChars (RSet.singleton c)
string cs  = REAppend $ map (REChars . RSet.singleton) cs

instance (Ord c, Enum c, Bounded c) => C.Kleene (RE c) where
    empty      = empty
    eps        = eps
    appends    = appends
    unions     = unions
    star       = star

instance (Ord c, Enum c, Bounded c) => C.CharKleene c (RE c) where
    char       = char

instance (Ord c, Enum c, Bounded c) => C.FiniteKleene c (RE c) where
    everything = everything
    charRange  = charRange
    fromRSet   = REChars
    anyChar    = anyChar

-------------------------------------------------------------------------------
-- Pseudo lattice
-------------------------------------------------------------------------------

(\/) :: (Ord c, Enum c, Bounded c) => RE c -> RE c -> RE c
r \/ r' = unions [r, r']

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
nullable :: RE c -> Bool
nullable (REChars _)      = False
nullable (REAppend rs)    = all nullable rs
nullable (REUnion _cs rs) = any nullable rs
nullable (REStar _)       = True

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
derivate :: (Ord c, Enum c, Bounded c) => c -> RE c -> RE c
derivate c (REChars cs)     = derivateChars c cs
derivate c (REUnion cs rs)  = unions $ derivateChars c cs : [ derivate c r | r <- toList rs]
derivate c (REAppend rs)    = derivateAppend c rs
derivate c rs@(REStar r)    = derivate c r <> rs

derivateAppend :: (Ord c, Enum c, Bounded c) => c -> [RE c] -> RE c
derivateAppend _ []      = empty
derivateAppend c [r]     = derivate c r
derivateAppend c (r:rs)
    | nullable r         = unions [r' <> appends rs, rs']
    | otherwise          = r' <> appends rs
  where
    r'  = derivate c r
    rs' = derivateAppend c rs

derivateChars :: Ord c =>  c -> RSet c -> RE c
derivateChars c cs
    | c `RSet.member` cs      = eps
    | otherwise               = empty

instance (Ord c, Enum c, Bounded c) => C.Derivate c (RE c) where
    nullable = nullable
    derivate = derivate

instance (Ord c, Enum c, Bounded c) => C.Match c (RE c) where
    match r = nullable . foldl' (flip derivate) r

-------------------------------------------------------------------------------
-- Nullable with proof
-------------------------------------------------------------------------------

-- | Not only we can decide whether 'RE' is nullable, we can also
-- remove the empty string:
--
-- >>> putPretty $ nullableProof eps
-- ^[]$
--
-- >>> putPretty $ nullableProof $ star "x"
-- ^xx*$
--
-- >>> putPretty $ nullableProof "foo"
-- Nothing
--
-- 'nullableProof' is consistent with 'nullable':
--
-- prop> isJust (nullableProof r) === nullable (asREChar r)
--
-- The returned regular expression is not nullable:
--
-- prop> maybe True (not . nullable) $ nullableProof $ asREChar r
--
-- If we union with empty regex, we get a equivalent regular expression
-- we started with:
--
-- prop> maybe r (eps \/) (nullableProof r) `equivalent` (asREChar r)
--
nullableProof :: forall c. (Ord c, Enum c, Bounded c) => RE c -> Maybe (RE c)
nullableProof (REChars _)   = Nothing

nullableProof (REAppend []) = Just empty
nullableProof (REAppend xs)
    | Just ys <- traverse (\x -> (,) x <$> nullableProof x) xs = Just (go ys)
    | otherwise = Nothing
  where
    go :: [(RE c, RE c)] -> RE c
    go rs = unions $ map appends $ tail $ traverse (\(r,r') -> [r,r']) rs

nullableProof (REUnion cs rs)
    | any nullable rs = Just $ REUnion cs $ Set.map (\r -> maybe r id $ nullableProof r) rs
    | otherwise       = Nothing

nullableProof (REStar r)
    | Just r' <- nullableProof r = Just (r' <> REStar r')
    | otherwise                  = Just (r <> REStar r) 

-------------------------------------------------------------------------------
-- isEmpty
-------------------------------------------------------------------------------

-- | Whether 'RE' is (structurally) equal to 'empty'.
--
-- prop> isEmpty r === all (not . nullable) (Map.keys $ transitionMap $ asREChar r)
isEmpty :: RE c -> Bool
isEmpty (REChars rs) = RSet.null rs
isEmpty _            = False

-------------------------------------------------------------------------------
-- States
-------------------------------------------------------------------------------

-- | Transition map. Used to construct 'Kleene.DFA.DFA'.
--
-- >>> void $ Map.traverseWithKey (\k v -> putStrLn $ pretty k ++ " : " ++ SF.showSF (fmap pretty v)) $ transitionMap ("ab" :: RE Char)
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
    => RE c
    -> Map (RE c) (SF.SF c (RE c))
transitionMap re = go Map.empty [re] where
    go :: Map (RE c) (SF.SF c (RE c))
       -> [RE c]
       -> Map (RE c) (SF.SF c (RE c))
    go !acc [] = acc
    go acc (r : rs)
        | r `Map.member` acc = go acc rs
        | otherwise = go (Map.insert r pm acc) (SF.values pm ++ rs)
      where
        pm = P.toSF (\c -> derivate c r) (leadingChars r)

instance (Ord c, Enum c, Bounded c) => C.TransitionMap c (RE c) where
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
leadingChars :: (Ord c, Enum c, Bounded c) => RE c -> P.Partition c
leadingChars (REChars cs)    = P.fromRSet cs
leadingChars (REUnion cs rs) = P.fromRSet cs <> foldMap leadingChars rs
leadingChars (REStar r)      = leadingChars r
leadingChars (REAppend rs)   = leadingCharsAppend rs

leadingCharsAppend :: (Ord c, Enum c, Bounded c) => [RE c] -> P.Partition c
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
-- 'equivalent' re1 re2 <=> forall s. 'match' re1 s === 'match' re1 s
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
equivalent :: forall c. (Ord c, Enum c, Bounded c) => RE c -> RE c -> Bool
equivalent x0 y0 = go mempty [(x0, y0)] where
    go :: Set (RE c, RE c) -> [(RE c, RE c)] -> Bool
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

    agree :: (RE c, RE c) -> Bool
    agree (x, y) = nullable x == nullable y

instance (Ord c, Enum c, Bounded c) => C.Equivalent c (RE c) where
    equivalent = equivalent

-------------------------------------------------------------------------------
-- Generation
-------------------------------------------------------------------------------

-- | Generate random strings of the language @RE c@ describes.
--
-- >>> let example = traverse_ print . take 3 . generate (curry QC.choose) 42
-- >>> example "abc"
-- "abc"
-- "abc"
-- "abc"
--
-- >>> example $ star $ "a" \/ "b"
-- "aaaaba"
-- "bbba"
-- "abbbbaaaa"
--
-- >>> example empty
--
-- prop> all (match r) $ take 10 $ generate (curry QC.choose) 42 (r :: RE Char)
--
generate
    :: (c -> c -> QC.Gen c) -- ^ character range generator
    -> Int    -- ^ seed
    -> RE c
    -> [[c]]  -- ^ infinite list of results
generate c seed re
    | isEmpty re = []
    | otherwise  = QC.unGen (QC.infiniteListOf (generator c re)) (QC.mkQCGen seed) 10

generator
    :: (c -> c -> QC.Gen c)
    -> RE c
    -> QC.Gen [c]
generator c = go where
    go (REChars cs)    = goChars cs
    go (REAppend rs)   = concat <$> traverse go rs
    go (REUnion cs rs)
        | RSet.null  cs = QC.oneof [ go r | r <- toList rs ]
        | otherwise     = QC.oneof $ goChars cs : [ go r | r <- toList rs ]
    go (REStar r)      = QC.sized $ \n -> do
        n' <- QC.choose (0, n)
        concat <$> sequence (replicate n' (go r))

    goChars cs = pure <$> QC.oneof [ c x y | (x,y) <- RSet.toRangeList cs ]

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Eq c => Semigroup (RE c) where
    r <> r' = appends [r, r']

instance Eq c => Monoid (RE c) where
    mempty  = eps
    mappend = (<>)
    mconcat = appends



instance c ~ Char => IsString (RE c) where
    fromString = string

instance (Ord c, Enum c, Bounded c, QC.Arbitrary c) => QC.Arbitrary (RE c) where
    arbitrary = QC.sized arb where
        c :: QC.Gen (RE c)
        c = REChars . RSet.fromRangeList <$> QC.arbitrary

        arb :: Int -> QC.Gen (RE c)
        arb n | n <= 0    = QC.oneof [c, fmap char QC.arbitrary, pure eps]
              | otherwise = QC.oneof
            [ c
            , pure eps
            , fmap char QC.arbitrary
            , liftA2 (<>) (arb n2) (arb n2)
            , liftA2 (\/) (arb n2) (arb n2)
            , fmap star (arb n2)
            ]
          where
            n2 = n `div` 2

    shrink (REUnion _cs rs) = Set.toList rs
    shrink (REAppend rs)    = rs ++ map appends (QC.shrink rs)
    shrink (REStar r)       = r : map star (QC.shrink r)
    shrink _                = []

instance (QC.CoArbitrary c) => QC.CoArbitrary (RE c) where
    coarbitrary (REChars cs)    = QC.variant (0 :: Int) . QC.coarbitrary (RSet.toRangeList cs)
    coarbitrary (REAppend rs)   = QC.variant (1 :: Int) . QC.coarbitrary rs
    coarbitrary (REUnion cs rs) = QC.variant (2 :: Int) . QC.coarbitrary (RSet.toRangeList cs, Set.toList rs)
    coarbitrary (REStar r)      = QC.variant (3 :: Int) . QC.coarbitrary r

-------------------------------------------------------------------------------
-- JavaScript
-------------------------------------------------------------------------------

instance c ~ Char => Pretty (RE c) where
    prettyS x = showChar '^' . go False x . showChar '$'
      where
        go :: Bool -> RE Char -> ShowS
        go p (REStar a)
            = parens p
            $ go True a . showChar '*'
        go p (REAppend rs)
            = parens p $ goMany id rs
        go p (REUnion cs rs)
            | RSet.null cs = goUnion p rs
            | Set.null rs  = prettyS cs
            | otherwise    = goUnion p (Set.insert (REChars cs) rs)
        go _ (REChars cs)
            = prettyS cs

        goUnion p rs
            | Set.member eps rs = parens p $ goUnion' True . showChar '?'
            | otherwise         = goUnion' p
          where
            goUnion' p' = case Set.toList (Set.delete eps rs) of
                [] -> go True empty
                [r] -> go p' r
                (r:rs') -> parens True $ goSome1 (showChar '|') r rs'

        goMany :: ShowS -> [RE Char] -> ShowS
        goMany sep = foldr (\a b -> go False a . sep . b) id

        goSome1 :: ShowS -> RE Char -> [RE Char] -> ShowS
        goSome1 sep r = foldl (\a b -> a . sep . go False b) (go False r)

        parens :: Bool -> ShowS -> ShowS
        parens True  s = showString "(" . s . showChar ')'
        parens False s = s

-------------------------------------------------------------------------------
-- Latin1
-------------------------------------------------------------------------------

instance C.ToLatin1 RE where
    toLatin1 (REChars rs)    = C.fromRSet (C.toLatin1 rs)
    toLatin1 (REAppend xs)   = appends (map C.toLatin1 xs)
    toLatin1 (REUnion rs xs) = C.fromRSet (C.toLatin1 rs) \/ unions (map C.toLatin1 (Set.toList  xs))
    toLatin1 (REStar r)      = star (C.toLatin1 r)

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Control.Monad (void)
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.List (sort)
-- >>> import Data.Maybe (isJust)
--
-- >>> import Test.QuickCheck ((===))
-- >>> import qualified Test.QuickCheck as QC
--
-- >>> import Kleene.Classes (match)
-- >>> import Algebra.Lattice (bottom)
-- >>> import Kleene.RE ()
--
-- >>> let asREChar :: RE Char -> RE Char; asREChar = id

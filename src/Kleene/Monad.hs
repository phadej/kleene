{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE Safe                   #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Kleene.Monad (
    M (..),
    -- * Construction
    --
    -- | Binary operators are
    --
    -- * '<>' for append
    --
    -- There are no binary operator for union. Use 'unions'.
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
    -- * Generation
    generate,
    -- * Conversion
    toKleene,
    -- * Other
    isEmpty,
    isEps,
    ) where

import Data.Semigroup (Semigroup (..))
import Prelude ()
import Prelude.Compat

import Control.Applicative (liftA2)
import Control.Monad       (ap)
import Data.Foldable       (toList)
import Data.List           (foldl')
import Data.String         (IsString (..))

import qualified Test.QuickCheck        as QC
import qualified Test.QuickCheck.Gen    as QC (unGen)
import qualified Test.QuickCheck.Random as QC (mkQCGen)

import qualified Kleene.Classes         as C
import           Kleene.Internal.Pretty

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.List (sort)
-- >>> import Kleene.Internal.Pretty (putPretty)
--
-- >>> import Test.QuickCheck ((===))
-- >>> import qualified Test.QuickCheck as QC
--
-- >>> import Kleene.RE (RE)
-- >>> import Kleene.Classes (match)
-- >>> let asMBool :: M Bool -> M Bool; asMBool = id

-- | Regular expression which has no restrictions on the elements.
-- Therefore we can have 'Monad' instance, i.e. have a regexp where
-- characters are regexps themselves.
--
-- Because there are no optimisations, it's better to work over small alphabets.
-- On the other hand, we can work over infinite alphabets, if we only
-- use small amount of symbols!
--
-- >>> putPretty $ string [True, False]
-- ^10$
--
-- >>> let re  = string [True, False, True]
-- >>> let re' = re >>= \b -> if b then char () else star (char ())
-- >>> putPretty re'
-- ^..*.$
--
data M c
    = MChars [c]        -- ^ One of the characters
    | MAppend [M c]     -- ^ Concatenation
    | MUnion [c] [M c]  -- ^ Union
    | MStar (M c)       -- ^ Kleene star
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative M where
    pure = MChars . pure
    (<*>) = ap

instance Monad M where
    return = pure

    MChars []    >>= _  = MChars []
    MChars cs    >>= k  = appends (map k cs)
    MAppend rs   >>= k  = appends (map (>>= k) rs)
    MUnion cs rs >>= k  = unions (map (>>= k) (MChars cs : rs))
    MStar r      >>= k  = star (r >>= k)

-------------------------------------------------------------------------------
-- Smart constructor
-------------------------------------------------------------------------------

-- | Empty regex. Doesn't accept anything.
--
-- >>> putPretty (empty :: M Bool)
-- ^[]$
--
-- prop> match (empty :: M Char) (s :: String) === False
--
empty :: M c
empty = MChars []

-- | Empty string. /Note:/ different than 'empty'.
--
-- >>> putPretty (eps :: M Bool)
-- ^$
--
-- >>> putPretty (mempty :: M Bool)
-- ^$
--
-- prop> match (eps :: M Char) s === null (s :: String)
--
eps :: M c
eps = MAppend []

-- |
--
-- >>> putPretty (char 'x')
-- ^x$
--
char :: c -> M c
char = MChars . pure

-- | /Note:/ we know little about @c@.
--
-- >>> putPretty $ charRange 'a' 'z'
-- ^[abcdefghijklmnopqrstuvwxyz]$
--
charRange :: Enum c => c -> c -> M c
charRange c c' = MChars [c .. c']


-- | Any character. /Note:/ different than dot!
--
-- >>> putPretty (anyChar :: M Bool)
-- ^[01]$
--
anyChar :: (Bounded c, Enum c) => M c
anyChar = MChars [minBound .. maxBound]

-- | Concatenate regular expressions.
--
appends :: [M c] -> M c
appends rs0
    | any isEmpty rs1 = empty
    | otherwise = case rs1 of
        [r] -> r
        rs  -> MAppend rs
  where
    -- flatten one level of MAppend
    rs1 = concatMap f rs0

    f (MAppend rs) = rs
    f r             = [r]

-- | Union of regular expressions.
--
-- Lattice laws don't hold structurally:
--
unions :: [M c] -> M c
unions = uncurry mk . foldMap f where
    mk cs rss
        | null rss = MChars cs
        | null cs = case rss of
            []  -> empty
            [r] -> r
            _   -> MUnion cs rss
        | otherwise    = MUnion cs rss

    f (MUnion cs rs) = (cs, rs)
    f (MChars cs)    = (cs, [])
    f r              = ([], [r])

-- | Kleene star.
--
star :: M c -> M c
star r = case r of
    MStar _                    -> r
    MAppend []                 -> eps
    MChars cs | null cs        -> eps
    MUnion cs rs | any isEps rs -> case rs' of
        []             -> star (MChars cs)
        [r'] | null cs -> star r'
        _              -> MStar (MUnion cs rs')
      where
        rs' = filter (not . isEps) rs
    _                          -> MStar r

-- | Literal string.
--
-- >>> putPretty ("foobar" :: M Char)
-- ^foobar$
--
-- >>> putPretty ("(.)" :: M Char)
-- ^\(\.\)$
--
-- >>> putPretty $ string [False, True]
-- ^01$
--
string :: [c] -> M c
string []  = eps
string [c] = MChars [c]
string cs  = MAppend $ map (MChars . pure) cs

instance C.Kleene  (M c) where
    empty      = empty
    eps        = eps
    appends    = appends
    unions     = unions
    star       = star

instance C.CharKleene c (M c) where
    char       = char

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
nullable :: M c -> Bool
nullable (MChars _)      = False
nullable (MAppend rs)    = all nullable rs
nullable (MUnion _cs rs) = any nullable rs
nullable (MStar _)       = True

-- | Intuitively, the derivative of a language \(\mathcal{L} \subset \Sigma^\star\)
-- with respect to a symbol \(a \in \Sigma\) is the language that includes only
-- those suffixes of strings with a leading symbol \(a\) in \(\mathcal{L}\).
--
-- >>> putPretty $ derivate 'f' "foobar"
-- ^oobar$
--
-- >>> putPretty $ derivate 'x' $ unions ["xyz", "abc"]
-- ^yz$
--
-- >>> putPretty $ derivate 'x' $ star "xyz"
-- ^yz(xyz)*$
--
derivate :: (Eq c, Enum c, Bounded c) => c -> M c -> M c
derivate c (MChars cs)     = derivateChars c cs
derivate c (MUnion cs rs)  = unions $ derivateChars c cs : [ derivate c r | r <- toList rs]
derivate c (MAppend rs)    = derivateAppend c rs
derivate c rs@(MStar r)    = derivate c r <> rs

derivateAppend :: (Eq c, Enum c, Bounded c) => c -> [M c] -> M c
derivateAppend _ []      = empty
derivateAppend c [r]     = derivate c r
derivateAppend c (r:rs)
    | nullable r         = unions [r' <> appends rs, rs']
    | otherwise          = r' <> appends rs
  where
    r'  = derivate c r
    rs' = derivateAppend c rs

derivateChars :: Eq c =>  c -> [c] -> M c
derivateChars c cs
    | c `elem` cs = eps
    | otherwise   = empty

instance (Eq c, Enum c, Bounded c) => C.Derivate c (M c) where
    nullable = nullable
    derivate = derivate

instance (Eq c, Enum c, Bounded c) => C.Match c (M c) where
    match r = nullable . foldl' (flip derivate) r

-------------------------------------------------------------------------------
-- isEmpty
-------------------------------------------------------------------------------

-- | Whether 'M' is (structurally) equal to 'empty'.
isEmpty :: M c -> Bool
isEmpty (MChars rs) = null rs
isEmpty _           = False

-- | Whether 'M' is (structurally) equal to 'eps'.
isEps :: M c -> Bool
isEps (MAppend rs) = null rs
isEps _            = False

-------------------------------------------------------------------------------
-- Generation
-------------------------------------------------------------------------------

-- | Generate random strings of the language @M c@ describes.
--
-- >>> let example = traverse_ print . take 3 . generate 42
-- >>> example "abc"
-- "abc"
-- "abc"
-- "abc"
--
-- >>> example $ star $ unions ["a", "b"]
-- ""
-- "abababaaba"
-- "a"
--
-- xx >>> example empty
--
-- expensive-prop> all (match r) $ take 10 $ generate 42 (r :: M Bool)
--
generate
    :: Int    -- ^ seed
    -> M c
    -> [[c]]  -- ^ infinite list of results
generate seed re
    | isEmpty re = []
    | otherwise  = QC.unGen (QC.infiniteListOf (generator re)) (QC.mkQCGen seed) 10

generator :: M c -> QC.Gen [c]
generator = go where
    go (MChars cs)    = goChars cs
    go (MAppend rs)   = concat <$> traverse go rs
    go (MUnion cs rs)
        | null cs   = QC.oneof [ go r | r <- toList rs ]
        | otherwise = QC.oneof $ goChars cs : [ go r | r <- toList rs ]
    go (MStar r)      = QC.sized $ \n -> do
        n' <- QC.choose (0, n)
        concat <$> sequence (replicate n' (go r))

    goChars cs = pure <$> QC.elements cs

-------------------------------------------------------------------------------
-- Conversion
-------------------------------------------------------------------------------

-- | Convert to 'Kleene'
--
-- >>> let re = charRange 'a' 'z'
-- >>> putPretty re
-- ^[abcdefghijklmnopqrstuvwxyz]$
--
-- >>> putPretty (toKleene re :: RE Char)
-- ^[a-z]$
--
toKleene :: C.CharKleene c k => M c -> k
toKleene (MChars cs)    = C.oneof cs
toKleene (MAppend rs)   = C.appends (map toKleene rs)
toKleene (MUnion cs rs) = C.unions (C.oneof cs : map toKleene rs)
toKleene (MStar r)      = C.star (toKleene r)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semigroup (M c) where
    r <> r' = appends [r, r']

instance Monoid (M c) where
    mempty  = eps
    mappend = (<>)
    mconcat = appends

instance c ~ Char => IsString (M c) where
    fromString = string

instance (Eq c, Enum c, Bounded c, QC.Arbitrary c) => QC.Arbitrary (M c) where
    arbitrary = QC.sized arb where
        c :: QC.Gen (M c)
        c = MChars <$> QC.arbitrary

        arb :: Int -> QC.Gen (M c)
        arb n | n <= 0    = QC.oneof [c, fmap char QC.arbitrary, pure eps]
              | otherwise = QC.oneof
            [ c
            , pure eps
            , fmap char QC.arbitrary
            , liftA2 (<>) (arb n2) (arb n2)
            , liftA2 (\x y -> unions [x,y]) (arb n2) (arb n2)
            , fmap star (arb n2)
            ]
          where
            n2 = n `div` 2

instance (QC.CoArbitrary c) => QC.CoArbitrary (M c) where
    coarbitrary (MChars cs)    = QC.variant (0 :: Int) . QC.coarbitrary cs
    coarbitrary (MAppend rs)   = QC.variant (1 :: Int) . QC.coarbitrary rs
    coarbitrary (MUnion cs rs) = QC.variant (2 :: Int) . QC.coarbitrary (cs, rs)
    coarbitrary (MStar r)      = QC.variant (3 :: Int) . QC.coarbitrary r

-------------------------------------------------------------------------------
-- JavaScript
-------------------------------------------------------------------------------

instance (Pretty c, Eq c) => Pretty (M c) where
    prettyS x = showChar '^' . go False x . showChar '$'
      where
        go :: Bool -> M c -> ShowS
        go p (MStar a)
            = parens p
            $ go True a . showChar '*'
        go p (MAppend rs)
            = parens p $ goMany id rs
        go p (MUnion cs rs)
            | null cs   = goUnion p rs
            | null rs   = prettySList cs
            | otherwise = goUnion p (MChars cs : rs)
        go _ (MChars cs)
            = prettySList cs

        goUnion p rs
            | elem eps rs = parens p $ goUnion' True . showChar '?'
            | otherwise   = goUnion' p
          where
            goUnion' p' = case filter (/= eps) rs of
                []      -> go True empty
                [r]     -> go p' r
                (r:rs') -> parens True $ goSome1 (showChar '|') r rs'

        goMany :: ShowS -> [M c] -> ShowS
        goMany sep = foldr (\a b -> go False a . sep . b) id

        goSome1 :: ShowS -> M c -> [M c] -> ShowS
        goSome1 sep r = foldl (\a b -> a . sep . go False b) (go False r)

        parens :: Bool -> ShowS -> ShowS
        parens True  s = showString "(" . s . showChar ')'
        parens False s = s

        prettySList :: [c] -> ShowS
        prettySList [c] = prettyS c
        prettySList xs  = showChar '[' . foldr (\a b -> prettyS a . b) (showChar ']') xs

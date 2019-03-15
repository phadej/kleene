{-# LANGUAGE CPP   #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe  #-}
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

import Prelude ()
import Prelude.Compat

import Control.Applicative (Alternative (..), liftA2)
import Data.Foldable       (toList)
import Data.RangeSet.Map   (RSet)
import Data.String         (IsString (..))

import qualified Data.RangeSet.Map      as RSet
import qualified Text.Regex.Applicative as R

import qualified Kleene.Classes         as C
import           Kleene.Internal.Pretty
import           Kleene.Internal.Sets
import qualified Kleene.RE              as RE

-- | Star behaviour
data Greediness
    = Greedy    -- ^ 'many'
    | NonGreedy -- ^ 'few'
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | 'Applicative' 'Functor' regular expression.
data K c a where
    KEmpty  :: K c a
    KPure   :: a -> K c a
    KChar   :: (Ord c, Enum c) => RSet c -> K c c
    KAppend :: (a -> b -> r) -> K c a -> K c b -> K c r
    KUnion  :: K c a -> K c a -> K c a
    KStar   :: Greediness -> K c a -> K c [a]

    -- optimisations
    KMap    :: (a -> b) -> K c a -> K c b -- could use Pure and Append
    KString :: Eq c => [c] -> K c [c]     -- could use Char and Append

instance (c ~ Char, IsString a) => IsString (K c a) where
    fromString s = KMap fromString (KString s)

instance Functor (K c) where
    fmap _ KEmpty          = KEmpty
    fmap f (KPure x)       = KPure (f x)
    fmap f (KMap g k)      = KMap (f . g) k
    fmap f (KAppend g a b) = KAppend (\x y -> f (g x y)) a b
    fmap f k                    = KMap f k

instance Applicative (K c) where
    pure = KPure

    KEmpty <*> _ = KEmpty
    _ <*> KEmpty = KEmpty

    KPure f <*> k = fmap f k
    k <*> KPure x = fmap ($ x) k

    f <*> x = KAppend ($) f x

#if MIN_VERSION_base(4,10,0)
    liftA2 = KAppend
#endif

instance Alternative (K c) where
    empty = KEmpty

    KEmpty <|> k = k
    k <|> KEmpty = k
    KChar a <|> KChar b = KChar (RSet.union a b)

    a <|> b = KUnion a b

    many KEmpty      = KPure []
    many (KStar _ k) = KMap pure (KStar Greedy k)
    many k           = KStar Greedy k

    some KEmpty      = KEmpty
    some (KStar _ k) = KMap pure (KStar Greedy k)
    some k           = liftA2 (:) k (KStar Greedy k)

-- | 'few', not 'many'.
--
-- Let's define two similar regexps
--
-- >>> let re1 = liftA2 (,) (few  $ char 'a') (many $ char 'a')
-- >>> let re2 = liftA2 (,) (many $ char 'a') (few  $ char 'a')
--
-- Their 'RE' behaviour is the same:
--
-- >>> C.equivalent (toRE re1) (toRE re2)
-- True
--
-- >>> map (C.match $ toRE re1) ["aaa","bbb"]
-- [True,False]
--
-- However, the 'RA' behaviour is different!
--
-- >>> R.match (toRA re1) "aaaa"
-- Just ("","aaaa")
--
-- >>> R.match (toRA re2) "aaaa"
-- Just ("aaaa","")
--
few :: K c a -> K c [a]
few KEmpty      = KPure []
few (KStar _ k) = KMap pure (KStar NonGreedy k)
few k           = KStar NonGreedy k

-------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------

-- | >>> putPretty anyChar
-- ^[^]$
anyChar :: (Ord c, Enum c, Bounded c) => K c c
anyChar = KChar RSet.full

-- | >>> putPretty $ oneof ("foobar" :: [Char])
-- ^[a-bfor]$
oneof :: (Ord c, Enum c, Foldable f) => f c -> K c c
oneof = KChar . RSet.fromList . toList

-- | >>> putPretty $ char 'x'
-- ^x$
char :: (Ord c, Enum c) => c -> K c c
char = KChar . RSet.singleton

-- | >>> putPretty $ charRange 'a' 'z'
-- ^[a-z]$
charRange :: (Enum c, Ord c) => c -> c -> K c c
charRange a b = KChar (RSet.singletonRange (a, b))

-- | >>> putPretty dot
-- ^.$
dot :: K Char Char
dot = KChar dotRSet

-- | >>> putPretty everything
-- ^[^]*$
everything :: (Ord c, Enum c, Bounded c) => K c [c]
everything = many anyChar

-- | >>> putPretty everything1
-- ^[^][^]*$
everything1 :: (Ord c, Enum c, Bounded c) => K c [c]
everything1 = some anyChar

-- | Matches nothing?
isEmpty :: (Ord c, Enum c, Bounded c) => K c a -> Bool
isEmpty k = C.equivalent (toRE k) C.empty

-- | Matches whole input?
isEverything :: (Ord c, Enum c, Bounded c) => K c a -> Bool
isEverything k = C.equivalent (toRE k) C.everything

-------------------------------------------------------------------------------
-- Matching
-------------------------------------------------------------------------------

-- | Match using @regex-applicative@
match :: K c a -> [c] -> Maybe a
match = R.match . toRA

-------------------------------------------------------------------------------
-- RE
-------------------------------------------------------------------------------

-- | Convert to 'RE'.
--
-- >>> putPretty (toRE $ many "foo" :: RE.RE Char)
-- ^(foo)*$
--
toRE :: (Ord c, Enum c, Bounded c) => K c a -> RE.RE c
toRE = toKleene

-- | Convert to any 'Kleene'
toKleene :: C.FiniteKleene c k => K c a -> k
toKleene (KMap _ a)      = toKleene a
toKleene (KUnion a b)    = C.unions [toKleene a, toKleene b]
toKleene (KAppend _ a b) = C.appends [toKleene a, toKleene b]
toKleene (KStar _ a)     = C.star (toKleene a)
toKleene (KString s)     = C.appends (map C.char s)
toKleene KEmpty          = C.empty
toKleene (KPure _)       = C.eps
toKleene (KChar cs)      = C.fromRSet cs

-- | Convert from 'RE'.
--
-- /Note:/ all 'RE.REStar's are converted to 'Greedy' ones,
-- it doesn't matter, as we don't capture anything.
--
-- >>> match (fromRE "foobar") "foobar"
-- Just "foobar"
--
-- >>> match (fromRE $ C.star "a" <> C.star "a") "aaaa"
-- Just "aaaa"
--
fromRE :: (Ord c, Enum c) => RE.RE c -> K c [c]
fromRE (RE.REChars cs)    = pure <$> KChar cs
fromRE (RE.REAppend rs)   = concat <$> traverse fromRE rs
fromRE (RE.REUnion cs rs) = foldr (KUnion . fromRE) (pure <$> KChar cs) (toList rs)
fromRE (RE.REStar r)      = concat <$> KStar Greedy (fromRE r)

-------------------------------------------------------------------------------
-- regex-applicative
-------------------------------------------------------------------------------

-- | Convert 'K' to 'R.RE' from @regex-applicative@.
--
-- >>> R.match (toRA ("xx" *> everything <* "zz" :: K Char String)) "xxyyyzz"
-- Just "yyy"
--
-- See also 'match'.
--
toRA :: K c a -> R.RE c a
toRA KEmpty              = empty
toRA (KPure x)           = pure x
toRA (KChar cs)          = R.psym (\c -> RSet.member c cs)
toRA (KAppend f a b)     = liftA2 f (toRA a) (toRA b)
toRA (KUnion a b)        = toRA a <|> toRA b
toRA (KStar Greedy a)    = many (toRA a)
toRA (KStar NonGreedy a) = R.few (toRA a)
toRA (KMap f a)          = fmap f (toRA a)
toRA (KString s)         = R.string s

-------------------------------------------------------------------------------
-- JavaScript
-------------------------------------------------------------------------------

-- | Convert to non-matching JavaScript string which can be used
-- as an argument to @new RegExp@
--
-- >>> putPretty ("foobar" :: K Char String)
-- ^foobar$
--
-- >>> putPretty $ many ("foobar" :: K Char String)
-- ^(foobar)*$
--
instance c ~ Char => Pretty (K c a) where
    pretty = pretty . toRE

-------------------------------------------------------------------------------
-- Doctest
-------------------------------------------------------------------------------

-- $setup
--
-- >>> :set -XOverloadedStrings

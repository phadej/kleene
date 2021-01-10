{-# LANGUAGE CPP   #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe  #-}
module Kleene.Functor.NonEmpty (
    K1,
    Greediness (..),
    -- * Constructors
    some1,
    few1,
    anyChar,
    oneof,
    char,
    charRange,
    dot,
    everything1,
    string,
    -- * Queries
    isEmpty,
    isEverything,
    -- * Matching
    match,
    -- * Conversions
    toRE,
    toKleene,
    toRA,
    nullableProof,
    ) where

import Prelude ()
import Prelude.Compat

import Control.Applicative (Alternative (..), liftA2)
import Data.Foldable       (toList)
import Data.Functor.Alt    ((<!>))
import Data.Functor.Apply  (Apply (..))
import Data.List.NonEmpty  (NonEmpty (..))
import Data.RangeSet.Map   (RSet)

import qualified Data.Functor.Alt       as Alt
import qualified Data.List.NonEmpty     as NE
import qualified Data.RangeSet.Map      as RSet
import qualified Text.Regex.Applicative as R

import qualified Kleene.Classes          as C
import           Kleene.Internal.Functor (Greediness (..), K (..))
import           Kleene.Internal.Pretty
import           Kleene.Internal.Sets
import qualified Kleene.RE               as RE

-- $setup
--
-- >>> import Control.Applicative (optional, Alternative (..))
-- >>> import Data.Functor.Apply (Apply (..))
-- >>> import Data.List.NonEmpty (NonEmpty (..))
-- >>> import Kleene.Functor (Greediness (..), K (..))
-- >>> import Data.Foldable (toList)
-- >>> import Kleene.Internal.Pretty (putPretty)
-- >>> import qualified Kleene.RE as RE
-- >>> import qualified Kleene.Classes as C
-- >>> import qualified Text.Regex.Applicative as R

-- | 'Applicative' 'Functor' regular expression.
data K1 c a where
    K1Empty  :: K1 c a
    K1Char   :: (Ord c, Enum c) => RSet c -> K1 c c
    K1Append :: (a -> b -> r) -> K1 c a -> K1 c b -> K1 c r
    K1Union  :: K1 c a -> K1 c a -> K1 c a
    KPlus    :: Greediness -> K1 c a -> K1 c (NonEmpty a)

    -- optimisations
    K1Map    :: (a -> b) -> K1 c a -> K1 c b -- could use Pure and Append
    K1String :: Eq c => NonEmpty c -> K1 c (NonEmpty c)     -- could use Char and Append

instance Functor (K1 c) where
    fmap _ K1Empty          = K1Empty
    fmap f (K1Map g k)      = K1Map (f . g) k
    fmap f (K1Append g a b) = K1Append (\x y -> f (g x y)) a b
    fmap f k                = K1Map f k

instance Apply (K1 c) where
    K1Empty <.> _ = K1Empty
    _ <.> K1Empty = K1Empty

    f <.> x = K1Append ($) f x

    liftF2 = K1Append

instance Alt.Alt (K1 c) where
    K1Empty <!> k = k
    k <!> K1Empty = k
    K1Char a <!> K1Char b = K1Char (RSet.union a b)

    a <!> b = K1Union a b

--
some1 :: K1 c a -> K1 c (NonEmpty a)
some1 K1Empty     = K1Empty
some1 (KPlus _ k) = K1Map pure (KPlus Greedy k)
some1 k           = KPlus Greedy k

-- | 'few1', not 'some1'.
--
-- Let's define two similar regexps
--
-- >>> let re1 = liftF2 (,) (few1 $ char 'a')  (some1 $ char 'a')
-- >>> let re2 = liftF2 (,) (some1 $ char 'a') (few1  $ char 'a')
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
-- >>> R.match (toRA re1) "aaaaa"
-- Just ('a' :| "",'a' :| "aaa")
--
-- >>> R.match (toRA re2) "aaaaa"
-- Just ('a' :| "aaa",'a' :| "")
--
few1 :: K1 c a -> K1 c (NonEmpty a)
few1 K1Empty     = K1Empty
few1 (KPlus _ k) = K1Map pure (KPlus NonGreedy k)
few1 k           = KPlus NonGreedy k

-------------------------------------------------------------------------------
--
-------------------------------------------------------------------------------

-- | >>> putPretty anyChar
-- ^[^]$
anyChar :: (Ord c, Enum c, Bounded c) => K1 c c
anyChar = K1Char RSet.full

-- | >>> putPretty $ oneof ("foobar" :: [Char])
-- ^[a-bfor]$
oneof :: (Ord c, Enum c, Foldable f) => f c -> K1 c c
oneof = K1Char . RSet.fromList . toList

-- | >>> putPretty $ char 'x'
-- ^x$
char :: (Ord c, Enum c) => c -> K1 c c
char = K1Char . RSet.singleton

-- | >>> putPretty $ charRange 'a' 'z'
-- ^[a-z]$
charRange :: (Enum c, Ord c) => c -> c -> K1 c c
charRange a b = K1Char (RSet.singletonRange (a, b))

-- | >>> putPretty dot
-- ^.$
dot :: K1 Char Char
dot = K1Char dotRSet

-- | >>> putPretty everything1
-- ^[^][^]*$
everything1 :: (Ord c, Enum c, Bounded c) => K1 c (NonEmpty c)
everything1 = some1 anyChar

-- | Matches nothing?
isEmpty :: (Ord c, Enum c, Bounded c) => K1 c a -> Bool
isEmpty k = C.equivalent (toRE k) C.empty

-- | Matches whole input?
isEverything :: (Ord c, Enum c, Bounded c) => K1 c a -> Bool
isEverything k = C.equivalent (toRE k) C.everything

string :: String -> K1 Char (NonEmpty Char)
string []       = error "panic! K1.string []"
string (x : xs) = K1String (x :| xs)

-------------------------------------------------------------------------------
-- Matching
-------------------------------------------------------------------------------

-- | Match using @regex-applicative@
match :: K1 c a -> [c] -> Maybe a
match = R.match . toRA

-------------------------------------------------------------------------------
-- RE
-------------------------------------------------------------------------------

-- | Convert to 'RE'.
--
-- >>> putPretty (toRE $ some1 (string "foo") :: RE.RE Char)
-- ^foo(foo)*$
--
toRE :: (Ord c, Enum c, Bounded c) => K1 c a -> RE.RE c
toRE = toKleene

-- | Convert to any 'Kleene'
toKleene :: C.FiniteKleene c k => K1 c a -> k
toKleene (K1Map _ a)      = toKleene a
toKleene (K1Union a b)    = C.unions [toKleene a, toKleene b]
toKleene (K1Append _ a b) = C.appends [toKleene a, toKleene b]
toKleene (KPlus _ a)      = let k = toKleene a in C.appends [k, C.star k]
toKleene (K1String s)     = C.appends (map C.char $ NE.toList s)
toKleene K1Empty          = C.empty
toKleene (K1Char cs)      = C.fromRSet cs

-------------------------------------------------------------------------------
-- regex-applicative
-------------------------------------------------------------------------------

-- | Convert 'K' to 'R.RE' from @regex-applicative@.
--
-- >>> R.match (toRA (string "xx" .> everything1 <. string "zz" :: K1 Char (NonEmpty Char))) "xxyyzyyzz"
-- Just ('y' :| "yzyy")
--
-- See also 'match'.
--
toRA :: K1 c a -> R.RE c a
toRA K1Empty              = empty
toRA (K1Char cs)          = R.psym (\c -> RSet.member c cs)
toRA (K1Append f a b)     = liftA2 f (toRA a) (toRA b)
toRA (K1Union a b)        = toRA a <|> toRA b
toRA (KPlus Greedy a)     = (:|) <$> toRA a <*> many (toRA a)
toRA (KPlus NonGreedy a)  = (:|) <$> toRA a <*> R.few (toRA a)
toRA (K1Map f a)          = fmap f (toRA a)
toRA (K1String (x :| xs)) = (:|) <$> R.sym x <*> R.string xs

-------------------------------------------------------------------------------
-- nullableProof
-------------------------------------------------------------------------------

-- |
-- >>> putPretty $ nullableProof (pure True)
-- Right 1 , ^[]$
--
-- >>> putPretty $ nullableProof (many "xyz" :: K Char [String])
-- Right [] , ^xyz(xyz)*$
--
-- >>> putPretty $ nullableProof (many $ toList <$> optional "x" <|> many "yz" :: K Char [[String]])
-- Right [] , ^(x|yz(yz)*)(x|yz(yz)*)*$
--
nullableProof :: K c a -> Either (K1 c a) (a, K1 c a)
nullableProof KEmpty    = Left K1Empty
nullableProof (KPure x) = Right (x, K1Empty)
nullableProof (KChar c) = Left (K1Char c)

nullableProof (KAppend f a b) = case (nullableProof a, nullableProof b) of
    (Left x, Left y)               -> Left (K1Append f x y)
    (Left x, Right (y', y))        -> Left ((`f` y') <$> x <!> K1Append f x y)
    (Right (x', x), Left y)        -> Left (K1Append f x y <!> f x' <$> y)
    (Right (x', x), Right (y', y)) -> Right
        (f x' y'
        , K1Append f x y
        <!> flip f y' <$> x
        <!> f x' <$> y
        )

nullableProof (KUnion a b) = case (nullableProof a, nullableProof b) of
    (Left x', Left _)              -> Left x'
    (Right (x, x'), Left y')       -> Right (x, x' <!> y')
    (Left x', Right (y, y'))       -> Right (y, x' <!> y')
    (Right (x, x'), Right (_, y')) -> Right (x, x' <!> y')

nullableProof (KStar g a) = case nullableProof a of
    Left x       -> Right ([], NE.toList <$> star1 x)
    Right (_, x) -> Right ([], NE.toList <$> star1 x) -- note, we don't left recurse
  where
    star1 = case g of
        Greedy    -> some1
        NonGreedy -> few1

nullableProof (KMap f a) = case nullableProof a of
    Right (x, x') -> Right (f x, fmap f x')
    Left x'       -> Left (fmap f x')

nullableProof (KString [])       = Right ([], K1Empty)
nullableProof (KString (c : cs)) = Left (NE.toList <$> K1String (c :| cs))

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
instance c ~ Char => Pretty (K1 c a) where
    pretty = pretty . toRE

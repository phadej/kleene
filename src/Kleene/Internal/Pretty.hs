{-# LANGUAGE GADTs #-}
{-# LANGUAGE Safe  #-}
{-# OPTIONS_HADDOCK not-home #-}
module Kleene.Internal.Pretty (
    Pretty (..),
    putPretty,
    ) where

import Prelude ()
import Prelude.Compat

import Data.Monoid          (Endo (..))
import Data.RangeSet.Map    (RSet)
import Kleene.Internal.Sets (dotRSet)

import qualified Data.RangeSet.Map as RSet

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

-- | Pretty class.
--
-- For @'pretty' :: 'Kleene.RE.RE' -> 'String'@ gives a
-- representation accepted by many regex engines.
--
class Pretty a where
    pretty :: a -> String
    pretty x = prettyS x ""

    prettyS :: a -> ShowS
    prettyS = showString . pretty

    {-# MINIMAL pretty | prettyS #-}

-- | @'putStrLn' . 'pretty'@
putPretty :: Pretty a => a -> IO ()
putPretty = putStrLn . pretty

instance c ~ Char => Pretty (RSet c) where
    prettyS cs
        | RSet.size cs == 1 = prettyS (head (RSet.elems cs))
        | cs == dotRSet  = showChar '.'
        | ics == dotRSet = showString "[^.]"
        | RSet.size cs < RSet.size ics = prettyRSet True cs
        | otherwise                    = prettyRSet False ics
      where
        ics = RSet.complement cs

prettyRSet :: Bool -> RSet Char -> ShowS
prettyRSet c cs
    = showChar '['
    . (if c then id else showChar '^')
    . appEndo (foldMap (Endo . f) (RSet.toRangeList cs))
    . showChar ']'
  where
    f (a, b)
      | a == b = prettyS a
      | otherwise = prettyS a . showChar '-' . prettyS b

-- | Escapes special regexp characters
instance Pretty Char where
    prettyS '.' = showString "\\."
    prettyS '-' = showString "\\-"
    prettyS '^' = showString "\\^"
    prettyS '*' = showString "\\*"
    prettyS '+' = showString "\\+"
    prettyS '?' = showString "\\?"
    prettyS '(' = showString "\\("
    prettyS ')' = showString "\\)"
    prettyS '[' = showString "\\["
    prettyS ']' = showString "\\]"
    prettyS '\r' = showString "\\r"
    prettyS '\n' = showString "\\n"
    prettyS '\t' = showString "\\t"
    prettyS c   = showChar c

instance Pretty Bool where
    prettyS True  = showChar '1'
    prettyS False = showChar '0'

instance Pretty () where
    prettyS _ = showChar '.'

instance Pretty a => Pretty (Maybe a) where
    prettyS Nothing  = showString "Nothing"
    prettyS (Just x) = prettyS x

instance (Pretty a, Pretty b) => Pretty (Either a b) where
    prettyS (Left x)  = showString "Left " . prettyS x
    prettyS (Right x) = showString "Right " . prettyS x

instance (Pretty a, Pretty b) => Pretty (a, b) where
    prettyS (x, y) = prettyS x . showString " , " . prettyS y

instance Show a => Pretty [a] where
    prettyS = showList

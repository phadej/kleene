{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE Trustworthy                #-}
{-# LANGUAGE UndecidableInstances       #-}
module Kleene.Equiv where

import Prelude ()
import Prelude.Compat

import Algebra.Lattice
       (BoundedJoinSemiLattice (..), JoinSemiLattice (..), joinLeq)
import Algebra.PartialOrd (PartialOrd (..))
import Data.Semigroup (Semigroup (..))

import Kleene.Classes
import           Kleene.Internal.Pretty

-- | Regular-expressions for which '==' is 'equivalent'.
--
-- >>> let re1 = star "a" <> "a" :: RE Char
-- >>> let re2 = "a" <> star "a" :: RE Char
--
-- >>> re1 == re2
-- False
--
-- >>> Equiv re1 == Equiv re2
-- True
--
-- 'Equiv' is also a 'PartialOrd' (but not 'Ord'!)
--
-- >>> Equiv "a" `leq` Equiv (star "a" :: RE Char)
-- True
--
-- Not all regular expessions are 'comparable':
--
-- >>> let reA = Equiv "a" :: Equiv RE Char
-- >>> let reB = Equiv "b" :: Equiv RE Char
-- >>> (leq reA reB, leq reB reA)
-- (False,False)
--
newtype Equiv r c = Equiv (r c)
  deriving (Show, Semigroup, Monoid, BoundedJoinSemiLattice, JoinSemiLattice, Pretty)

instance Equivalent c (r c) => Eq (Equiv r c) where
    (==) = equivalent

-- | \(a \preceq b := a \lor b = b \)
instance (JoinSemiLattice (r c), Equivalent c (r c)) => PartialOrd (Equiv r c) where
    leq = joinLeq

deriving instance Kleene       (r c) => Kleene       (Equiv r c)
deriving instance CharKleene c (r c) => CharKleene c (Equiv r c)
deriving instance Derivate   c (r c) => Derivate   c (Equiv r c)
deriving instance Match      c (r c) => Match      c (Equiv r c)
deriving instance Equivalent c (r c) => Equivalent c (Equiv r c)
deriving instance Complement c (r c) => Complement c (Equiv r c)

-- $setup
-- >>> import Kleene.RE (RE)

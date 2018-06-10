{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Algebra.Lattice
import Criterion.Main
import Data.Binary
import Data.Semigroup
import Data.Vector     ((!))
import Data.Word       (Word8)
import GHC.Generics    (Generic)
import Data.Coerce (coerce)
import Kleene
import Data.ByteString (ByteString)
import Foreign (Ptr)
import Foreign.C.Types (CChar(..), CSize(..), CUChar(..))

import qualified Data.Binary
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Unsafe
import qualified Foreign.Marshal.Unsafe

import qualified Data.Set as Set
import qualified Data.Function.Step.Discrete.Closed as SF
import qualified Data.Map as Map
import qualified Data.ByteString as BS
import qualified Data.Vector

import Data.Binary (Binary(..))
import Data.ByteString (ByteString)
import Data.Vector ((!))
import Data.Word (Word8)
import Foreign (Ptr)
import Foreign.C.Types (CChar(..), CSize(..), CUChar(..))
import GHC.Generics (Generic)

import qualified Control.Concurrent
import qualified Control.Parallel.Strategies
import qualified Data.Binary
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Unsafe
import qualified Data.ByteString
import qualified Data.Vector
import qualified Foreign
import qualified Foreign.Marshal.Unsafe

-------------------------------------------------------------------------------
-- Inputs
-------------------------------------------------------------------------------

len :: Int
len = 2 * 1000 * 1000

contents :: String
contents = "/*" ++ replicate len ' ' ++ "*/"

contentsBS :: BS.ByteString
contentsBS = BS.pack $ [slash8, star8] ++ replicate len space8 ++ [star8, slash8]

slash8 :: Word8
slash8 = 47

star8  :: Word8
star8 = 42

space8 :: Word8
space8 = 32

-------------------------------------------------------------------------------
-- Languages
-------------------------------------------------------------------------------

ere :: ERE Char
ere = star $
    "/*" <> endsWith "*/"
    \/ notChar '/'
    \/ char '/' <> notChar '*'

without :: (FiniteKleene c k, Complement c k) => k -> k
without c  = complement (everything <> c <> everything)

endsWith :: (FiniteKleene c k, Complement c k) => k -> k
endsWith c = without c <> c

dfa :: DFA Int Char
dfa = fromTM ere

ere8 :: ERE Word8
ere8 = star $
    string [slash8, star8] <> endsWith (string [star8, slash8])
    \/ notChar slash8
    \/ char slash8 <> notChar star8

dfa8 :: DFA Int Word8
dfa8 = fromTM ere8

dfaS :: DFA State Word8
Just dfaS = toState dfa8 -- !!! unsafe

-------------------------------------------------------------------------------
-- Gabriel stuff
-------------------------------------------------------------------------------

data State
    = S00 | S01 | S02 | S03 | S04 | S05 | S06 | S07
    | S08 | S09 | S10 | S11 | S12 | S13 | S14 | S15
  deriving (Binary, Bounded, Enum, Eq, Generic, Ord, Show)

-- Split out a state transition into its own type
newtype Transition = Transition { runTransition :: State -> State }

numberOfStates :: Int
numberOfStates = fromEnum (maxBound :: State) + 1

instance Semigroup Transition where
    Transition f <> Transition g = Transition (g . f)

instance Monoid Transition where
    mempty = Transition id
    mappend = (<>)

instance Binary Transition where
    put (Transition f) = mapM_ (put . f) [minBound..maxBound]

    get = do
        !ss <- Data.Vector.replicateM numberOfStates get
        return (Transition (\s -> ss ! fromEnum s))

newtype StateMachine = StateMachine { runStateMachine :: Word8 -> Transition }

instance Binary StateMachine where
    put (StateMachine k) = mapM_ (put . k) [minBound..maxBound]

    get = do
        let numBytes = fromEnum (maxBound :: Word8) + 1
        ts <- Data.Vector.replicateM numBytes get
        return (StateMachine (\word8 -> ts ! fromEnum word8))

runSerial :: StateMachine -> ByteString -> Transition
runSerial stateMachine input = Foreign.Marshal.Unsafe.unsafeLocalState io
  where
    step = Data.ByteString.Lazy.toStrict (Data.Binary.encode stateMachine)

    io =
        Data.ByteString.Unsafe.unsafeUseAsCStringLen step  $ \(ptrStep , _  ) ->
        Data.ByteString.Unsafe.unsafeUseAsCStringLen input $ \(ptrBytes, len) ->
        Foreign.allocaBytes numberOfStates                 $ \ptrOut          -> do
            let c_len = fromIntegral len
            c_run ptrBytes c_len ptrStep ptrOut
            bytes <- Data.ByteString.packCStringLen (ptrOut, numberOfStates)
            return (Data.Binary.decode (Data.ByteString.Lazy.fromStrict bytes))

run :: Int
    -- ^ Number of threads to use
    -> StateMachine
    -- ^ State machine to run over the input bytes
    -> ByteString
    -- ^ Input bytes to feed to the state machine
    -> Transition
    -- ^ Computed function from every starting state to every final state
run 1          matrix bytes = runSerial matrix bytes
run numThreads matrix bytes =
    mconcat
        (Control.Parallel.Strategies.parMap
            Control.Parallel.Strategies.rseq
            (runSerial matrix)
            (chunkBytes subLen bytes) )
  where
    len = Data.ByteString.length bytes

    subLen = ((len - 1) `div` numThreads) + 1

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toState :: DFA Int Word8 -> Maybe (DFA State Word8)
toState = traverseState $ \i ->
    if 0 <= i && i < numberOfStates
    then Just (toEnum i)
    else Nothing

toStateMachine :: DFA State Word8 -> StateMachine
toStateMachine (DFA tr _ _ _) = coerce f
  where
    f :: Word8 -> State -> State
    f w s = maybe s (SF.! w) $ Map.lookup s tr

matchSerial :: DFA State Word8 -> ByteString -> Bool
matchSerial dfa@(DFA _ ini acc _) bs = 
    case runSerial (toStateMachine dfa) bs of
        Transition f -> Set.member (f ini) acc

matchParallel :: Int -> DFA State Word8 -> ByteString -> Bool
matchParallel n dfa@(DFA _ ini acc _) bs = 
    case run n (toStateMachine dfa) bs of
        Transition f -> Set.member (f ini) acc

-------------------------------------------------------------------------------
-- Main
-------------------------------------------------------------------------------

main :: IO ()
main = do
    print $ match ere contents
    print $ match dfa contents
    print $ match8 dfa8 contentsBS
    print $ matchSerial dfaS contentsBS
    print $ matchParallel 2 dfaS contentsBS

    defaultMain $ pure $ bgroup "match"
        [ bench "ere"  $ whnf (match ere)   contents
        , bench "dfa"  $ whnf (match dfa)   contents
        , bench "dfa8" $ whnf (match8 dfa8) contentsBS
        , bench "dfaS" $ whnf (matchSerial dfaS) contentsBS
        , bench "dfaP" $ whnf (matchParallel 2 dfaS) contentsBS
        ]

-- | Split a `ByteString` into chunks of size @n@
chunkBytes :: Int -> ByteString -> [ByteString]
chunkBytes n bytes =
    if Data.ByteString.null bytes
    then []
    else prefix : chunkBytes n suffix
  where
    ~(prefix, suffix) = Data.ByteString.splitAt n bytes

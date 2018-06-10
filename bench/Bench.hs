{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Criterion.Main
import Kleene
import Data.Semigroup
import Algebra.Lattice

contents :: String
contents = "/*" ++ replicate 1000000 ' ' ++ "*/"

ere :: ERE Char
ere = star $
    "/*" <> endsWith "*/"
    \/ notChar '/'
    \/ char '/' <> notChar '*'
  where
    without c  = complement (everything <> c <> everything)
    endsWith c = without c <> c

dfa :: DFA Int Char
dfa = fromTM ere

main :: IO ()
main = defaultMain $ pure $
    bgroup "match"
        [ bench "ere" $ whnf (match ere) contents
        , bench "dfa" $ whnf (match dfa) contents
        ]

{-# LANGUAGE CPP #-}
module Main (main) where

import Data.Bits        (shiftR, (.&.), (.|.))
import Data.Char        (ord)
import Data.Semigroup   ((<>))
import Data.Word        (Word8)
import Test.Tasty       (defaultMain, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

import Kleene
import Kleene.DFA (fromRE, toRE)

#if MIN_VERSION_bytestring(0,11,2)
import Test.Tasty.QuickCheck (label, testProperty, (===))

import qualified Data.ByteString as BS
#endif

main :: IO ()
main = do
    -- print utf8char2
    -- print utf8char3
    -- print utf8char4
    defaultMain $ testGroup "kleene-utf8"
        [ testCase "brute ≃ brute'" $ do
            assertBool "not equiv" (equivalent utf8char1 utf8char2)
        , testCase "brute' ≃ manual1" $ do
            assertBool "not equiv" (equivalent utf8char2 utf8char3)
        , testCase "manual1 ≃ manual2" $ do
            assertBool "not equiv" (equivalent utf8char3 utf8char4)
        , testCase "brute ≃ manual2" $ do
            assertBool "not equiv" (equivalent utf8char1 utf8char4)

#if MIN_VERSION_bytestring(0,11,2)
        , testProperty "isValidUtf8" $ \w8s ->
            let bs = BS.pack w8s
                isValid = BS.isValidUtf8 bs
            in label (show isValid) $ isValid === match (star utf8char4) w8s
#endif
        ]

-------------------------------------------------------------------------------
-- Bruteforce definition
-------------------------------------------------------------------------------

utf8char1 :: RE Word8
utf8char1 = unions
    [ string (encodeStringUtf8 [c])
    | c <- [ '\0' .. maxBound ]
    ]

-------------------------------------------------------------------------------
-- Derived definition
-------------------------------------------------------------------------------

utf8charDFA1 :: DFA Word8
utf8charDFA1 = fromRE utf8char1

utf8char2 :: RE Word8
utf8char2 = toRE utf8charDFA1

-------------------------------------------------------------------------------
-- Written out definition
-------------------------------------------------------------------------------

utf8char3 :: RE Word8
utf8char3 = unions
    [ charRange 0x00 0x7F
    , sub1 <> charRange 0x80 0xBF
    ]
  where
    sub1 = unions
        [ charRange 0xC2 0xDF
        , charRange 0xE0 0xE0 <> charRange 0xa0 0xBF
        , charRange 0xED 0xED <> charRange 0x80 0x9F
        , sub2 <> charRange 0x80 0xBF
        ]

    sub2 = unions
        [ charRange 0xE1 0xEC
        , charRange 0xEE 0xEF
        , charRange 0xF0 0xF0 <> charRange 0x90 0xBF
        , charRange 0xF1 0xF3 <> charRange 0x80 0xBF
        , charRange 0xF4 0xF4 <> charRange 0x80 0x8f
        ]

-------------------------------------------------------------------------------
-- Manual definition, how human would written it
-------------------------------------------------------------------------------

utf8char4 :: RE Word8
utf8char4 = unions
    [ charRange 0x00 0x7F
    , charRange 0xC2 0xDF <> charRange 0x80 0xBF
    , charRange 0xE0 0xE0 <> charRange 0xa0 0xBF <> charRange 0x80 0xBF
    , charRange 0xE1 0xEC <> charRange 0x80 0xBF <> charRange 0x80 0xBF
    , charRange 0xED 0xED <> charRange 0x80 0x9F <> charRange 0x80 0xBF
    , charRange 0xEE 0xEF <> charRange 0x80 0xBF <> charRange 0x80 0xBF
    , charRange 0xF0 0xF0 <> charRange 0x90 0xBF <> charRange 0x80 0xBF <> charRange 0x80 0xBF
    , charRange 0xF1 0xF3 <> charRange 0x80 0xBF <> charRange 0x80 0xBF <> charRange 0x80 0xBF
    , charRange 0xF4 0xF4 <> charRange 0x80 0x8f <> charRange 0x80 0xBF <> charRange 0x80 0xBF
    ]

-------------------------------------------------------------------------------
-- UTF8 encoding
-------------------------------------------------------------------------------

encodeStringUtf8 :: String -> [Word8]
encodeStringUtf8 []        = []
encodeStringUtf8 (c:cs)
  | c <= '\x07F' = w8
                 : encodeStringUtf8 cs
  | c <= '\x7FF' = (0xC0 .|.  w8ShiftR  6          )
                 : (0x80 .|. (w8          .&. 0x3F))
                 : encodeStringUtf8 cs
  | c <= '\xD7FF'= (0xE0 .|.  w8ShiftR 12          )
                 : (0x80 .|. (w8ShiftR  6 .&. 0x3F))
                 : (0x80 .|. (w8          .&. 0x3F))
                 : encodeStringUtf8 cs
  | c <= '\xDFFF'= 0xEF : 0xBF : 0xBD -- U+FFFD
                 : encodeStringUtf8 cs
  | c <= '\xFFFF'= (0xE0 .|.  w8ShiftR 12          )
                 : (0x80 .|. (w8ShiftR  6 .&. 0x3F))
                 : (0x80 .|. (w8          .&. 0x3F))
                 : encodeStringUtf8 cs
  | otherwise    = (0xf0 .|.  w8ShiftR 18          )
                 : (0x80 .|. (w8ShiftR 12 .&. 0x3F))
                 : (0x80 .|. (w8ShiftR  6 .&. 0x3F))
                 : (0x80 .|. (w8          .&. 0x3F))
                 : encodeStringUtf8 cs
  where
    w8 = fromIntegral (ord c) :: Word8
    w8ShiftR :: Int -> Word8
    w8ShiftR = fromIntegral . shiftR (ord c)

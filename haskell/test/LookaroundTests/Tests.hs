module LookaroundTests.Tests where

import Test.Hspec

import Data.Char (isAlphaNum, isLower, isUpper, isDigit)

import Utils
import Extracted (LRegex (..), scanMatch)

foo = fromWord "foo"
bar = fromWord "bar"

foolookbar = foo `Concat` LookAhead bar
lookfoobar = wildCard `Concat` LookBehind foo `Concat` bar
lookfoobar2 = LookBehind foo `Concat` bar


{-
    From: http://www.rexegg.com/regex-lookarounds.html

    1. The password must have between six and ten word characters \w
    2. It must include at least one lowercase character [a-z]
    3. It must include at least three uppercase characters [A-Z]
    4. It must include at least one digit 
-}

condition1 = repeatMN 6 10 (CharClass isWord)
condition2 = wildCard `Concat` (CharClass isLower) `Concat` wildCard
condition3 = repeatN 3 (wildCard `Concat` (CharClass  isUpper)) `Concat` wildCard
condition4 = wildCard `Concat` (CharClass isDigit) `Concat` wildCard
password = topAndMulti [condition1, condition2, condition3, condition4]

-- A lowercase word that does not use the letter 'q'
lowercaseWord = Star . CharClass $ isLower
containsq = wildCard `Concat` (CharClass  (== 'q')) `Concat` wildCard
wordNoQ = NegLookAhead containsq `Concat` lowercaseWord

-- a word that does not end with END
endswithEND = wildCard `Concat` fromWord "END"
doesnotEndwithEND = wildCard `Concat` NegLookBehind endswithEND

-- there are at least 3 uppercase letters which are immediately followed by a vowel
isVowel = CharClass  $ (`elem` "AEIOUaeiou")
upperthenvowel = (CharClass  isUpper) `Concat` LookAhead (isVowel `Concat` wildCard)
atleast3upperthenvowel = repeatN 3 (wildCard `Concat` upperthenvowel) `Concat` wildCard

-- a word that starts with START
startswithSTART = wildCard `Concat` LookBehind (fromWord "START") `Concat` wildCard

-- text between two underscores
twoUnderscores = fromWord "__"
textBetweenUnderscores = wildCard `Concat` LookBehind twoUnderscores `Concat` wildCard `Concat` LookAhead twoUnderscores `Concat` wildCard
textBetweenUnderscores2 = LookBehind twoUnderscores `Concat` wildCard `Concat` LookAhead twoUnderscores

-- a word whose second last character is X, but does not end withXY
xnoxy = wildCard `Concat` LookAhead (fromWord "X" `Concat` NegLookAhead (fromWord "Y") `Concat` (CharClass  $ const True) ) `Concat` wildCard

foobarTests :: SpecWith ()
foobarTests = do
    describe "Some tests for foo(?=bar)" $ do
        it "works correctly on foobar" $ do
            scanMatch foolookbar "foobar" `shouldBe` [False, False, False, True, False, False, False]
        it "works correctly on foobaz" $ do
            scanMatch foolookbar "foobaz" `shouldBe` [False, False, False, False, False, False, False]
        it "correctly extracts foo" $ do
            leftMostMaximalMatch foolookbar "foobar" `shouldBe` Just "foo"
            leftMostMaximalMatch foolookbar "foobaz" `shouldBe` Nothing
    describe "Some tests for .*(?<=foo)bar" $ do
        it "works correctly on foobar" $ do
            scanMatch lookfoobar "foobar" `shouldBe` [False, False, False, False, False, False, True]
        it "works correctly on foobaz" $ do
            scanMatch lookfoobar "foobaz" `shouldBe` [False, False, False, False, False, False, False]
    describe "Some tests for (?<=foo)bar" $ do
        it "can extract bar" $ do
            leftMostMaximalMatch lookfoobar2 "foobar" `shouldBe` Just "bar"
            leftMostMaximalMatch lookfoobar2 "foobaz" `shouldBe` Nothing


passwordTests :: SpecWith ()
passwordTests = do
    describe "Testing password conditions" $ do
        it "correctly checks \\w{6,10}" $ do
            "abcdef" `shouldSatisfy` match condition1
            "abcd-f" `shouldNotSatisfy` match condition1
            "abc" `shouldNotSatisfy` match condition1
        it "correctly checks presence of a lowercase character" $ do
            "abcdef" `shouldSatisfy` match condition2
            "ABCDEF" `shouldNotSatisfy` match condition2
            "ABCdEF" `shouldSatisfy` match condition2
        it "correctly checks presence of 3 uppercase characters" $ do
            "ABCDEF" `shouldSatisfy` match condition3
            "ABCdEF" `shouldSatisfy` match condition3
            "ABcde" `shouldNotSatisfy` match condition3
        it "correctly checks presence of a digit" $ do
            "abc123" `shouldSatisfy` match condition4
            "abc" `shouldNotSatisfy` match condition4
            "123" `shouldSatisfy` match condition4
            "a1b" `shouldSatisfy` match condition4
        it "correctly checks the conjunction of the conditions above" $ do
            "abc" `shouldNotSatisfy` match password -- too short
            "abc123" `shouldNotSatisfy` match password -- no uppercase
            "ABC123" `shouldNotSatisfy` match password -- no lowercase
            "abcDEF" `shouldNotSatisfy` match password -- no digit
            "abc123DE" `shouldNotSatisfy` match password -- not enough uppercase characters
            "abc123DEF" `shouldSatisfy` match password
            "abc123DEFghi" `shouldNotSatisfy` match password -- too long

booleanOpTests :: SpecWith ()
booleanOpTests = do
    describe "Checking several boolean operations" $ do
        it "correctly checks for lower case words without q" $ do
            "abc" `shouldSatisfy` match wordNoQ
            "abcq" `shouldNotSatisfy` match wordNoQ
            "qabc" `shouldNotSatisfy` match wordNoQ
            "ABC" `shouldNotSatisfy` match wordNoQ
        it "correctly checks for words that do not end with END" $ do
            "abc" `shouldSatisfy` match doesnotEndwithEND
            "abcEND" `shouldNotSatisfy` match doesnotEndwithEND
            "abcENDabc" `shouldSatisfy` match doesnotEndwithEND
            "abcENDabcEND" `shouldNotSatisfy` match doesnotEndwithEND
            "abcENDabcENDabc" `shouldSatisfy` match doesnotEndwithEND
        it "correctly checks for words containing at least 3 instances where an upper case letter is immediately followed by a vowel" $ do
            "AEIOU" `shouldSatisfy` match atleast3upperthenvowel
            "ABeAA" `shouldNotSatisfy` match atleast3upperthenvowel
            "ABeAAe" `shouldSatisfy` match atleast3upperthenvowel
            "AeAAe" `shouldSatisfy` match atleast3upperthenvowel
            "AeAAX" `shouldNotSatisfy` match atleast3upperthenvowel
            "AeAAXe" `shouldSatisfy` match atleast3upperthenvowel
        it "correctly checks for words that start with START" $ do
            "STARTabc" `shouldSatisfy` match startswithSTART
            "abcSTART" `shouldNotSatisfy` match startswithSTART
            "abcSTARTabc" `shouldNotSatisfy` match startswithSTART
        it "correctly checks for __words__ between two underscores" $ do
            "__abc__" `shouldSatisfy` match textBetweenUnderscores
            "__abc" `shouldNotSatisfy` match textBetweenUnderscores
            "abc__" `shouldNotSatisfy` match textBetweenUnderscores
            "__abc__def__" `shouldSatisfy` match textBetweenUnderscores
        it "correctly extracts the leftmost longest __word__ between two underscores" $ do
            leftMostMaximalMatch textBetweenUnderscores2 "__abc__def__" `shouldBe` Just "abc__def"
            leftMostMaximalMatch textBetweenUnderscores2 "__abc__" `shouldBe` Just "abc"
            leftMostMaximalMatch textBetweenUnderscores2 "x__abc__x" `shouldBe` Nothing
            leftMostMaximalMatch textBetweenUnderscores2 "__abc" `shouldBe` Nothing
            leftMostMaximalMatch textBetweenUnderscores2 "abc__" `shouldBe` Nothing
        it "correctly checks for words that end with X[^Y]" $ do
            "abcXZ" `shouldSatisfy` match xnoxy
            "abcXY" `shouldNotSatisfy` match xnoxy
            "abcXYabc" `shouldNotSatisfy` match xnoxy
            "abcXabc" `shouldNotSatisfy` match xnoxy

hardFamily = wildCard : map f hardFamily where
    f r = wildCard `topAnd` (wildCard `Concat` r `Concat` fromWord "b")

hardFamilyTests :: SpecWith ()
hardFamilyTests = do
    describe "Testing with r[i+1]= (?=.*r[i]b).*" $ do
        it "works correctly at level 2" $ do
            replicate 5000 'a' ++ "b" `shouldSatisfy` match (hardFamily !! 2)
            replicate 5000 'a' `shouldNotSatisfy` match (hardFamily !! 2)
        it "works correctly at level 10" $ do
            replicate 5000 'a' ++ "b" `shouldSatisfy` match (hardFamily !! 10)
            replicate 5000 'a' `shouldNotSatisfy` match (hardFamily !! 10)

{- 
    This is taken from the following paper:
    Derivatives of Regular Expressions with Lookahead, by T. Miyazaki \& Y. Minamide (2019) [JIP]

    Below we use the primes 2, 3, 5, 7, 11, 13. The size of the regular expression is no bigger than 2 + 3 + 5 + 7 + 11 + 13 <= 13 * 13 = 169.

    However, it represents that the string is a multiple of N, where
    N = 2 * 3 * 5 * 7 * 11 * 13 = 30030.

    The regex .*b.{N} can thus be described using a much smaller regex, as done below.
    We know that this regex, however, cannot be expressed with a DFA of less than 2^30030 states.

-}

primeProductRegex = topAndMulti $ map ofLength [2, 3, 5, 7, 11, 13] where
    ofLength n = Star $ repeatN n (CharClass $ const True)
buffer30030 = wildCard `Concat` fromWord "b" `Concat` primeProductRegex

primeProductTests :: SpecWith ()
primeProductTests = do
    describe "Testing ability to do multiplications" $ do
        it "correctly checks for multiples of 30030" $ do
            replicate 30030 'a' `shouldSatisfy` match primeProductRegex
            replicate 67 'a' `shouldNotSatisfy` match primeProductRegex
            replicate 60060 'a' `shouldSatisfy` match primeProductRegex
            replicate 2000 'a' `shouldNotSatisfy` match primeProductRegex
        it "correctly checks that the 30030th last letter is b" $ do
            "b" ++ replicate 30030 'a' `shouldSatisfy` match buffer30030
            "a" ++ replicate 30030 'a' `shouldNotSatisfy` match buffer30030
            "bb" ++ replicate 30030 'a' `shouldSatisfy` match buffer30030


lookaroundTest :: SpecWith ()
lookaroundTest = do
    foobarTests
    passwordTests
    booleanOpTests
    hardFamilyTests
    primeProductTests
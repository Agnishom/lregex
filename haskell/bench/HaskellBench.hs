{-# LANGUAGE NumericUnderscores #-}

module HaskellBench where

import Data.Maybe (isJust)
import Control.Monad
import System.Random
import System.Clock
import System.IO
import System.IO.Silently

import Utils
import Extracted (LRegex(..), llmatch)

import BenchUtils hiding (nestedXRe, nestedDisjRe, disjNegLookAheadRe, manyPlusRe, mkRe)

nestedXRe :: Int -> LRegex Char
nestedXRe n = wildCard `Concat` f n `Concat` wildCard
    where
        f 0 = Epsilon
        f 1 = LookAhead $ wildCard `Concat` (fromWord "c") `Concat` wildCard
        f n = LookAhead $ wildCard `Concat` (f (n - 1)) `Concat` wildCard

nestedDisjRe :: Int -> LRegex Char
nestedDisjRe n = wildCard `Concat` fromWord "a" `Concat` f n `Concat` wildCard
    where
        letters = map (:[]) ['b' .. 'z']
        f 0 = Epsilon
        f 1 = LookAhead $ wildCard `Concat` (fromWord "c") `Concat` wildCard
        f n = Union part1 part2 where
            part1 = wildCard `Concat` fromWord "a" `Concat` f (n - 1)
            part2 = LookAhead $ wildCard `Concat` (fromWord $ letters !! n) `Concat` wildCard

disjNegLookAheadRe :: Int -> LRegex Char
disjNegLookAheadRe n = r `Concat` wildCard
    where
    rs = drop 1 [ NegLookAhead (wildCard `Concat` fromWord [ch] `Concat` wildCard) | ch <- take n ['a'..]]
    r = foldl Union (NegLookAhead $ wildCard `Concat` fromWord "a" `Concat` wildCard) rs

manyPlusRe :: Int -> LRegex Char
manyPlusRe n = error "manyPlusRe: not implemented"

mkRe :: ReFamily -> Int -> LRegex Char
mkRe DisjNegLookAhead = disjNegLookAheadRe
mkRe NestedX = nestedXRe
mkRe NestedDisj = nestedDisjRe
mkRe ManyPlus = manyPlusRe

haskellBench :: ReFamily -> Int -> InpFamily -> Int -> IO BenchmarkResult
haskellBench reFamily reParam inpFamily inpParam = do
    let re = mkRe reFamily reParam
    let input = mkInput inpFamily inpParam
    let re_size = lreSize re
    silence . print $ re_size
    let input_length = length input
    silence . print $ input_length
    start <- getTime Monotonic
    let b = isJust (llmatch re input)
    silence $ print b
    end <- getTime Monotonic
    let diff_millis = toNanoSecs (end - start) `div` 1_000_000
    let time_in_ms = fromIntegral diff_millis
    return $ BenchmarkResult Haskell reFamily reParam inpFamily inpParam (Just time_in_ms)
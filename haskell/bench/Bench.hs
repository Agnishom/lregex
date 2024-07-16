
{-# LANGUAGE NumericUnderscores #-}

module Main (main) where

import qualified Streaming.Prelude as S
import Streaming (Stream, Of)

import BenchUtils
import HaskellBench (haskellBench)

bench :: Tool -> ReFamily -> Int -> InpFamily -> Int -> IO BenchmarkResult
bench Haskell = haskellBench
-- bench PCRE = pcre2Bench
-- bench Java = javaBench
-- bench Lean = leanBench

-- we let the string stay the same, but increase the parameter n
haskellParamsScaleRegex :: [(Tool, ReFamily, Int, InpFamily, Int)]
haskellParamsScaleRegex =
    [ (Haskell, DisjNegLookAhead, n, ManyZthenAtoY, len) | 
        n <- [1..10], len <- [ 50_000, 100_000 .. 200_000 ]
    ] ++
    [ (Haskell, NestedX, n, ManyA, len) |
        n <- [1..10], len <- [ 50_000, 100_000 .. 200_000 ]
    ] ++
    [ (Haskell, NestedDisj, n, ManyA, len) |
        n <- [1..10], len <- [ 50_000, 100_000 .. 200_000 ]
    ]

-- here, we increase the input length for the same regex
haskellParamsScaleInput :: [(Tool, ReFamily, Int, InpFamily, Int)]
haskellParamsScaleInput = 
    [ (Haskell, DisjNegLookAhead, n, ManyZthenAtoY, len) | 
        n <- [1..4], len <- [ 30_000, 60_000 .. 300_000 ]
    ] ++
    [ (Haskell, NestedX, n, ManyA, len) | 
        n <- [1..4], len <- [ 30_000, 60_000 .. 300_000 ]
    ] ++
    [ (Haskell, NestedDisj, n, ManyA, len) | 
        n <- [1..4], len <- [ 30_000, 60_000 .. 300_000]
    ]

benchParams :: [(Tool, ReFamily, Int, InpFamily, Int)]
-- benchParams = haskellParams ++ javaParams ++ pcreParams ++ leanParams
benchParams = haskellParamsScaleInput

nTrials :: Int
nTrials = 10

resultStream :: Stream (Of BenchmarkResult) IO ()
resultStream = S.mapM f . S.each . concat $ replicate nTrials benchParams
    where
        f = \(tool, reFamily, reParam, inpFamily, inpParam) -> bench tool reFamily reParam inpFamily inpParam

main :: IO ()
main = do
    putStrLn benchmarkHeader
    S.mapM_ (putStrLn . strBenchmarkResult) resultStream
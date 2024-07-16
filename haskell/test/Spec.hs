module Main (main) where

import LookaroundTests.Tests (lookaroundTest)

import Test.Hspec 

main :: IO ()
main = hspec $ do
    lookaroundTest

module Main where

import System.Environment

import Parser.Parser
import Utils
import Extracted

fromFile :: LRegex Char -> FilePath -> IO ()
fromFile re file = do
  contents <- readFile file
  print $ match re contents

interactRe :: LRegex Char -> IO ()
interactRe re = getLine >>= print . match re 

main :: IO ()
main = do
  args <- getArgs
  case args of
    [regex] -> case stringToLRe regex of
      Left err -> putStrLn err
      Right re -> interactRe re
    [regex, file] -> case stringToLRe regex of
      Left err -> putStrLn err
      Right re -> fromFile re file
    _ -> putStrLn "Usage: lookaroundre <regex> [file]"

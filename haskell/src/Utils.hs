module Utils where

import Data.Char (isAlphaNum, isLower, isUpper, isDigit)

import Extracted (LRegex (..), llmatch, scanMatch)

fromWord :: String -> LRegex Char
fromWord = foldl1 Concat . map (CharClass .  (==))

isWord :: (Char -> Bool) -- \w
isWord = \c -> c == '_' || isAlphaNum c

wildCard :: LRegex a
wildCard = Star . CharClass $ const True

multiConcat :: [LRegex a] -> LRegex a
multiConcat rs
    | null rs   = Epsilon
    | otherwise = foldr1 Concat rs

multiUnion :: [LRegex a] -> LRegex a
multiUnion = foldr1 Union

repeatN :: Int -> LRegex a -> LRegex a
repeatN n r = multiConcat $ replicate n r

repeatMN :: Int -> Int -> LRegex a -> LRegex a
repeatMN m n r = multiUnion [repeatN i r | i <- [m..n]]

atLeastN :: Int -> LRegex a -> LRegex a
atLeastN n r = repeatN n r `Concat` Star r

-- this construct only works as a conjunction if used at the top level

topAnd :: LRegex a -> LRegex a -> LRegex a
topAnd r1 r2 = LookAhead r2 `Concat` r1

topAndMulti :: [LRegex a] -> LRegex a
topAndMulti = foldr1 topAnd

topMinus :: LRegex a -> LRegex a -> LRegex a
topMinus r1 r2 = NegLookAhead r2 `Concat` r1

leftMostMaximalMatch :: LRegex a -> [a] -> Maybe [a]
leftMostMaximalMatch r w = 
    case llmatch r w of 
    Just (n, d) -> Just . take d . drop n $ w
    Nothing -> Nothing
        
match :: LRegex a -> [a] -> Bool
match r w = last (scanMatch r w)

lreSize :: LRegex a -> Int
lreSize Epsilon = 1
lreSize (CharClass _) = 1
lreSize (Concat r1 r2) = 1 + lreSize r1 + lreSize r2
lreSize (Union r1 r2) = 1 + lreSize r1 + lreSize r2
lreSize (Star r) = 1 + lreSize r
lreSize (LookAhead r) = 1 + lreSize r
lreSize (LookBehind r) = 1 + lreSize r
lreSize (NegLookAhead r) = 1 + lreSize r
lreSize (NegLookBehind r) = 1 + lreSize r

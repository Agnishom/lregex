{-

  Taken from the Skylighting Project
  https://github.com/jgm/skylighting/blob/master/skylighting-core/src/Regex/KDE/Compile.hs

-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Parser.Parser
  (compileRegex, toLRegex, stringToLRe)
  where

import Data.Word (Word8)
import qualified Data.ByteString as B
import Data.ByteString (ByteString)
import qualified Data.ByteString.UTF8 as U
import Safe
import Data.Attoparsec.ByteString as A hiding (match)
import Data.Char
import Control.Applicative
import Data.Functor
import Parser.Types
import Control.Monad
import Control.Monad.State.Strict
#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup ((<>))
#endif

import qualified Extracted as E (LRegex (..))
import Utils


stringToLRe :: String -> Either String (E.LRegex Char)
stringToLRe re = (compileRegex True . U.fromString $ re) >>= toLRegex

toLRegex :: Regex -> Either String (E.LRegex Char)
toLRegex MatchNull = Right E.Epsilon
toLRegex MatchAnyChar = Right $ E.CharClass (const True)
toLRegex (MatchChar f) = Right $ E.CharClass f
toLRegex (MatchConcat e f) = E.Concat <$> toLRegex e <*> toLRegex f
toLRegex (MatchAlt e f) = E.Union <$> toLRegex e <*> toLRegex f
toLRegex (MatchSome e) = atLeastN 1 <$> toLRegex e
toLRegex (MatchCount lo hi e) = repeatMN lo hi <$> toLRegex e
toLRegex (MatchCountUnbounded lo e) = atLeastN lo <$> toLRegex e
toLRegex AssertWordBoundary = Right $ E.LookAhead $ E.CharClass (isWordChar) `E.Concat` E.CharClass ( not . isWordChar)
toLRegex AssertBeginning = Right $ E.LookBehind E.Epsilon
toLRegex AssertEnd = Right $ E.LookAhead E.Epsilon
toLRegex (AssertPositive Forward e) = E.LookAhead <$> toLRegex e
toLRegex (AssertPositive Backward e) = E.LookBehind <$> toLRegex e
toLRegex (AssertNegative Forward e) = E.NegLookAhead <$> toLRegex e
toLRegex (AssertNegative Backward e) = E.NegLookBehind <$> toLRegex e
toLRegex (MatchDynamic _) = Left "dynamic regexes not supported"
toLRegex (MatchCapture _ e) = toLRegex e
toLRegex (MatchCaptured _) = Left "backreferences not supported"
toLRegex (Subroutine _) = Left "subroutines not supported"
toLRegex (Lazy e) = toLRegex e
toLRegex (Possessive e) = toLRegex e


-- | Compile a UTF-8 encoded ByteString as a Regex.  If the first
-- parameter is True, then the Regex will be case sensitive.
compileRegex :: Bool -> ByteString -> Either String Regex
compileRegex caseSensitive bs =
  let !res = parseOnly (evalStateT parser 0) bs
   in res
 where
   parser = do
     !re <- pRegex caseSensitive
     (re <$ lift A.endOfInput) <|>
       do rest <- lift A.takeByteString
          fail $ "parse error at byte position " ++
                 show (B.length bs - B.length rest)

type RParser = StateT Int Parser

pRegex :: Bool -> RParser Regex
pRegex caseSensitive =
  option MatchNull $
  foldr MatchAlt
    <$> (pAltPart caseSensitive)
    <*> (many $ lift (char '|') *> (pAltPart caseSensitive <|> pure mempty))

pAltPart :: Bool -> RParser Regex
pAltPart caseSensitive = mconcat <$> many1 (pRegexPart caseSensitive)

char :: Char -> Parser Char
char c =
  c <$ satisfy (== fromIntegral (ord c))

pRegexPart :: Bool -> RParser Regex
pRegexPart caseSensitive =
  (lift (pRegexChar caseSensitive) <|> pParenthesized caseSensitive) >>=
     lift . pSuffix

pParenthesized :: Bool -> RParser Regex
pParenthesized caseSensitive = do
  _ <- lift (satisfy (== 40))
  -- pcrepattern says: A group that starts with (?| resets the capturing
  -- parentheses numbers in each alternative.
  resetCaptureNumbers <- option False (True <$ lift (string "?|"))
  modifier <- if resetCaptureNumbers
                 then return id
                 else lift (satisfy (== 63) *> pGroupModifiers)
                    <|> (MatchCapture <$> (modify (+ 1) *> get))
  currentCaptureNumber <- get
  contents <- option MatchNull $
    foldr MatchAlt
      <$> (pAltPart caseSensitive)
      <*> (many $ lift (char '|') *>
            (((if resetCaptureNumbers
                  then put currentCaptureNumber
                  else return ()) >> pAltPart caseSensitive) <|> pure mempty))
  _ <- lift (satisfy (== 41))
  return $ modifier contents

pGroupModifiers :: Parser (Regex -> Regex)
pGroupModifiers =
  (id <$ char ':')
   <|>
     do dir <- option Forward $ Backward <$ char '<'
        (AssertPositive dir <$ char '=') <|> (AssertNegative dir <$ char '!')
   <|>
     do n <- satisfy (\d -> d >= 48 && d <= 57)
        return (\_ -> Subroutine (fromIntegral n - 48))
   <|>
     do _ <- satisfy (== 82) -- R
        return  (\_ -> Subroutine 0)

pSuffix :: Regex -> Parser Regex
pSuffix re = option re $ do
  w <- satisfy (\x -> x == 42 || x == 43 || x == 63 || x == 123)
  (case w of
    42  -> return $ MatchAlt (MatchSome re) MatchNull
    43  -> return $ MatchSome re
    63  -> return $ MatchAlt re MatchNull
    123 -> do
      let isDig x = x >= 48 && x < 58
      minn <- option Nothing $ readMay . U.toString <$> A.takeWhile isDig
      comma <- option False (char ',' $> True)
      maxn <- case comma of
                False -> pure Nothing
                True -> option Nothing (readMay . U.toString <$> A.takeWhile isDig)
      _ <- char '}'
      case (minn, comma, maxn) of
          (Nothing, _, Nothing) -> mzero
          (Just n, True, Nothing)  -> return $! atleast n re
          (Nothing, True, Just n)  -> return $! atmost n re
          (Just n, False, Nothing) -> return $! between n n re
          (Just m, True, Just n)   -> return $! between m n re
    _   -> fail "pSuffix encountered impossible byte") >>= pQuantifierModifier
 where
   atmost 0 _ = MatchNull
   atmost n r = MatchCount 0 n r

   between m n r = MatchCount m n r

   atleast n r = MatchCountUnbounded n r

pQuantifierModifier :: Regex -> Parser Regex
pQuantifierModifier re = option re $
  (Possessive re <$ satisfy (== 43)) <|>
  (Lazy re <$ satisfy (==63))

pRegexChar :: Bool -> Parser Regex
pRegexChar caseSensitive = do
  w <- satisfy $ const True
  case w of
    46  -> return MatchAnyChar
    37 -> (do -- dynamic %1 %2
              ds <- A.takeWhile1 (\x -> x >= 48 && x <= 57)
              case readMay (U.toString ds) of
                Just !n -> return $ MatchDynamic n
                Nothing -> fail "not a number")
            <|> return (MatchChar (== '%'))
    92  -> pRegexEscapedChar
    36  -> return AssertEnd
    94  -> return AssertBeginning
    91  -> pRegexCharClass
    _ | w < 128
      , not (isSpecial w)
         -> do let c = chr $ fromIntegral w
               return $! MatchChar $
                        if caseSensitive
                           then (== c)
                           else (\d -> toLower d == toLower c)
      | w >= 0xc0 -> do
          rest <- case w of
                    _ | w >= 0xf0 -> A.take 3
                      | w >= 0xe0 -> A.take 2
                      | otherwise -> A.take 1
          case U.uncons (B.cons w rest) of
            Just (d, _) -> return $! MatchChar $
                             if caseSensitive
                                then (== d)
                                else (\e -> toLower e == toLower d)
            Nothing     -> fail "could not decode as UTF8"
      | otherwise -> mzero

pRegexEscapedChar :: Parser Regex
pRegexEscapedChar = do
  c <- anyChar
  (case c of
    'b' -> return AssertWordBoundary
    '{' -> do -- captured pattern: \1 \2 \{12}
              ds <- A.takeWhile1 (\x -> x >= 48 && x <= 57)
              _ <- char '}'
              case readMay (U.toString ds) of
                Just !n -> return $ MatchCaptured $ n
                Nothing -> fail "not a number"
    'd' -> return $ MatchChar isDigit
    'D' -> return $ MatchChar (not . isDigit)
    's' -> return $ MatchChar isSpace
    'S' -> return $ MatchChar (not . isSpace)
    'w' -> return $ MatchChar isWordChar
    'W' -> return $ MatchChar (not . isWordChar)
    _ | isDigit c ->
       return $! MatchCaptured (ord c - ord '0')
      | otherwise -> mzero) <|> (MatchChar . (==) <$> pEscaped c)

pEscaped :: Char -> Parser Char
pEscaped c =
  case c of
    '\\' -> return c
    'a' -> return '\a'
    'f' -> return '\f'
    'n' -> return '\n'
    'r' -> return '\r'
    't' -> return '\t'
    'v' -> return '\v'
    'x' -> do -- \xhh matches hex hh, \x{h+} matches hex h+
      ds <- (satisfy (== 123) *> A.takeWhile (/= 125) <* satisfy (== 125))
             <|> ( do
                      x1 <- satisfy (inClass "a-fA-F0-9")
                      x2 <- Just <$> satisfy (inClass "a-fA-F0-9") <|> pure Nothing
                      case x2 of
                        Nothing -> return $ B.pack [x1]
                        Just x2' -> if inClass "a-fA-F0-9" x2'
                                    then return $ B.pack [x1, x2']
                                    else return $ B.pack [x1]
                  )
      case readMay ("'\\x" ++ U.toString ds ++ "'") of
        Just x  -> return x
        Nothing -> fail "invalid hex character escape"
    '0' -> do -- \0ooo matches octal ooo
      ds <- A.take 3
      case readMay ("'\\o" ++ U.toString ds ++ "'") of
        Just x  -> return x
        Nothing -> fail "invalid octal character escape"
    _ | c >= '1' && c <= '7' -> do
      -- \123 matches octal 123, \1 matches octal 1
      let octalDigitScanner s w
            | s < 3, w >= 48 && w <= 55
                        = Just (s + 1) -- digits 0-7
            | otherwise = Nothing
      ds <- A.scan (1 :: Int) octalDigitScanner
      case readMay ("'\\o" ++ [c] ++ U.toString ds ++ "'") of
        Just x  -> return x
        Nothing -> fail "invalid octal character escape"
    'z' -> do -- \zhhhh matches unicode hex char hhhh
      ds <- A.take 4
      case readMay ("'\\x" ++ U.toString ds ++ "'") of
        Just x  -> return x
        Nothing -> fail "invalid hex character escape"
    _ -> return c

pRegexCharClass :: Parser Regex
pRegexCharClass = do
  negated <- option False $ True <$ satisfy (== 94) -- '^'
  let getEscapedClass = do
        _ <- satisfy (== 92) -- backslash
        (isDigit <$ char 'd')
         <|> (not . isDigit <$ char 'D')
         <|> (isSpace <$ char 's')
         <|> (not . isSpace <$ char 'S')
         <|> (isWordChar <$ char 'w')
         <|> (not . isWordChar <$ char 'W')
  let getPosixClass = do
        _ <- string "[:"
        localNegated <- option False $ True <$ satisfy (== 94) -- '^'
        res <- (isAlphaNum <$ string "alnum")
             <|> (isAlpha <$ string "alpha")
             <|> (isAscii <$ string "ascii")
             <|> ((\c -> isSpace c && c `notElem` ['\n','\r','\f','\v']) <$
                   string "blank")
             <|> (isControl <$ string "cntrl")
             <|> ((\c -> isPrint c || isSpace c) <$ string "graph:")
             <|> (isLower <$ string "lower")
             <|> (isUpper <$ string "upper")
             <|> (isPrint <$ string "print")
             <|> (isPunctuation <$ string "punct")
             <|> (isSpace <$ string "space")
             <|> ((\c -> isAlphaNum c ||
                         generalCategory c == ConnectorPunctuation)
                   <$ string "word:")
             <|> (isHexDigit <$ string "xdigit")
        _ <- string ":]"
        return $! if localNegated then not . res else res
  let getC = (satisfy (== 92) *> anyChar >>= pEscaped) <|>
       (chr . fromIntegral <$> satisfy (\x -> x /= 92 && x /= 93)) -- \ ]
  let getCRange = do
        c <- getC
        (\d -> (\x -> x >= c && x <= d)) <$> (char '-' *> getC) <|>
          return (== c)
  brack <- option [] $ [(==']')] <$ char ']'
  fs <- many (getEscapedClass <|> getPosixClass <|> getCRange)
  _ <- satisfy (== 93) -- ]
  let f c = any ($ c) $ brack ++ fs
  return $! MatchChar (if negated then (not . f) else f)

anyChar :: Parser Char
anyChar = do
  w <- satisfy (const True)
  return $! chr $ fromIntegral w

isSpecial :: Word8 -> Bool
isSpecial 92 = True -- '\\'
isSpecial 63 = True -- '?'
isSpecial 42 = True -- '*'
isSpecial 43 = True -- '+'
-- isSpecial 123 = True -- '{'  -- this is okay except in suffixes
isSpecial 91 = True -- '['
isSpecial 93 = True -- ']'
isSpecial 37 = True -- '%'
isSpecial 40 = True -- '('
isSpecial 41 = True -- ')'
isSpecial 124 = True -- '|'
isSpecial 46 = True -- '.'
isSpecial 36 = True -- '$'
isSpecial 94 = True -- '^'
isSpecial _  = False

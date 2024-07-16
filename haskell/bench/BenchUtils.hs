module BenchUtils where

import Data.List (intercalate)

import System.Process
import System.Directory
import System.Exit

data Tool = Haskell -- | Java | PCRE | Lean
    deriving (Show, Eq)

data ReFamily = DisjNegLookAhead | NestedX | NestedDisj | ManyPlus
    deriving (Show, Eq)

data InpFamily = ManyA | ManyEthenABCD | ManyZthenAtoY
    deriving (Show, Eq)

data BenchmarkResult = BenchmarkResult{
        tool :: Tool,
        regex_family :: ReFamily,
        regex_param :: Int,
        input_family :: InpFamily,
        input_length :: Int,
        time_in_ms :: Maybe Double
        } deriving (Show)

benchmarkHeader :: String
benchmarkHeader = "tool,regex_family,regex_param,input_family,input_length,time_in_ms"

strBenchmarkResult :: BenchmarkResult -> String
strBenchmarkResult (BenchmarkResult tool regex_family regex_param input_family input_length time_in_ms) =
    intercalate "," [show tool, show regex_family, show regex_param, show input_family, show input_length, str_time_in_ms]
    where
    str_time_in_ms = case time_in_ms of
                        Just t -> show t
                        Nothing -> "NA"

mkInput :: InpFamily -> Int -> String
mkInput ManyA n = replicate n 'a'
mkInput ManyEthenABCD n = replicate n 'e' ++ "abcd"
mkInput ManyZthenAtoY n = replicate n 'z' ++ "abcdefghijklmnopqrstuvwy"

fileNameInput :: String -> InpFamily -> Int -> String
fileNameInput tmpPrefix ManyA n = tmpPrefix ++ "manyA" ++ show n
fileNameInput tmpPrefix ManyEthenABCD n = tmpPrefix ++ "manyEthenABCD" ++ show n
fileNameInput tmpPrefix ManyZthenAtoY n = tmpPrefix ++ "manyZthenAtoY" ++ show n

saveInput :: String -> InpFamily -> Int -> IO ()
saveInput tmpPrefix inpFamily n = do
    let filePath = fileNameInput tmpPrefix inpFamily n
    alreadyExists <- doesFileExist filePath
    if alreadyExists
    then return ()
    else do
        createDirectoryIfMissing True tmpPrefix
        let cmd = case inpFamily of
                    ManyA -> "for i in `seq 1 " ++ show n ++ "`; do echo -n a; done > " ++ filePath
                    ManyEthenABCD -> "(for i in `seq 1 " ++ show n ++ "`; do echo -n e; done; echo -n abcd) > " ++ filePath
                    ManyZthenAtoY -> "(for i in `seq 1 " ++ show n ++ "`; do echo -n z; done; echo -n abcdefghijklmnopqrstuvwy) > " ++ filePath
        (exitCode, _, _) <- readProcessWithExitCode "bash" ["-c", cmd] ""
        case exitCode of
            ExitSuccess -> return ()
            ExitFailure _ -> error "saveInput: failed to save input"

nestedXRe :: Int -> String
nestedXRe n = "a" ++ f n where
    f 0 = ""
    f 1 = "(?=.*c)"
    f n = "(?=.*" ++ f (n - 1) ++ ")"

nestedDisjRe :: Int -> String
nestedDisjRe n = "a" ++ f n where
    letters :: [String]
    letters = map (:[]) ['b' .. 'z']
    f 0 = ""
    f 1 = "(?=.*b)"
    f n = "((?=.*" ++ (letters !! (n - 1)) ++ ")|.*a" ++ f (n - 1) ++ ")"

disjNegLookAheadRe :: Int -> String
disjNegLookAheadRe n = r ++ ".*"
    where
    rs = drop 1 [ "(?!(.*" ++ [ch] ++ ".*))"  | ch <- take n ['a'..] ]
    r = foldl (\r s -> "(" ++ r ++ "|" ++ s ++ ")") "(?!(.*a.*))" rs

manyPlusRe :: Int -> String
manyPlusRe n = error "manyPlusRe: not implemented"

mkRe :: ReFamily -> Int -> String
mkRe DisjNegLookAhead = disjNegLookAheadRe
mkRe NestedX = nestedXRe
mkRe NestedDisj = nestedDisjRe
mkRe ManyPlus = manyPlusRe

fileNameRe :: String -> ReFamily -> Int -> String
fileNameRe tmpPrefix _ _ = tmpPrefix ++ "pattern.re"

saveRe :: String -> ReFamily -> Int -> IO ()
saveRe tmpPrefix reFamily n = do
    writeFile (fileNameRe tmpPrefix reFamily n) (mkRe reFamily n)
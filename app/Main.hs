module Main where

import           Interpreter
import           Parser
import           Text.Megaparsec
import           System.Environment
import           System.IO
import qualified Data.Text.IO as TIO

-- i gave up halfway through
main :: IO ()
main = do
    args <- getArgs
    if null args then putStrLn "Usage: hlox <filename>"
    else do
        let filename = head args
        handle <- openFile filename ReadMode
        contents <- TIO.hGetContents handle
        ret <- parse (fmtErrorsP filename contents runDecls declsP) filename contents
        putStrLn "temp"

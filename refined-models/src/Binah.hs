module Binah where

import ModelsParser
import Models

import Control.Monad
import Data.Char
import Data.List
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Printf


data Flag =
      Version    -- -v
    | Help       -- --help
    deriving (Eq, Ord, Enum, Show, Bounded)

version = "0.0"
help = "*TODO*"
usage = "Usage is: binah [refined-models]"

flags =
    [ Option ['v'] ["version"] (NoArg Version)
        "Prints the version number."
    , Option ['h'] ["help"] (NoArg Help)
        "Prints the help page."
    ]

runParser :: String -> IO ()
runParser file = do stmts <- parseFile file
                    mapM_ (putStr . prettyPrintStmt) stmts
                    

parse argv = case getOpt Permute flags argv of
    ([Version], _, []) -> putStrLn $ "Binah version " ++ version
    ([Help], _, []) -> putStrLn help 
    ([], [file], []) -> runParser file 
    _ -> putStrLn usage

run :: IO ()
run = do as <- getArgs
         parse as

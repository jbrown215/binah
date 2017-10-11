module Binah where

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

flags =
    [ Option ['v'] ["version"] (NoArg Version)
        "Prints the version number."
    , Option ['h'] ["help"] (NoArg Help)
        "Prints the help page."
    ]

parse argv = case getOpt Permute flags argv of
    ([Version], _, []) -> putStrLn $ "Binah version " ++ version
    ([Help], _, []) -> putStrLn help 
    _ -> putStrLn "Usage is: TODO"

run :: IO ()
run = do
    as <- getArgs
    parse as

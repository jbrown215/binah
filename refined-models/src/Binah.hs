module Binah where

import Models
import GenProofs

import Control.Monad
import Data.Char
import Data.List
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.IO
import Text.Printf


data Flag =
      Version    -- -v, --version
    | Help       -- -h, --help
    | Proofs     -- -p, --proofs
    deriving (Eq, Ord, Enum, Show, Bounded)

version = "0.0"
help = "*TODO*"
usage = "Usage is: binah [refined-models]"

flags =
    [ Option ['v'] ["version"] (NoArg Version)
        "Prints the version number."
    , Option ['h'] ["help"] (NoArg Help)
        "Prints the help page."
    , Option ['p'] ["proofs"] (NoArg Proofs)
        "Generates proofs for the models files."
    ]

parse argv = case getOpt Permute flags argv of
    ([Version], _, []) -> putStrLn $ "Binah version " ++ version
    ([Help], _, []) -> putStrLn help 
    ([Proofs], [file], []) -> makeProofs file
    ([], [file], []) -> makeModelsAndSpecFile file
    _ -> putStrLn usage

run :: IO ()
run = do as <- getArgs
         parse as

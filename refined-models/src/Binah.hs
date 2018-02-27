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
      Version            -- -v, --version
    | Help               -- -h, --help
    | Proofs             -- -p, --proofs
    | DecentralizedWorld -- -d, --decentralized-world
    | CentralizedWorld   -- -c, --centralized-world
    | Library            -- -l, --library
    deriving (Eq, Ord, Enum, Show, Bounded)

version = "0.0"
help = "Usage: binah path/to/refined-models will generate the models file and models.spec file.\n"
    ++ "Flags:\n"
    ++ "  -v     Print the version number\n"
    ++ "  -h     Print help information\n"
    ++ "  -p     Generate database program proofs\n"
    ++ "  -d     Generate decentralized world\n"
    ++ "  -c     Generate centralized world\n"
    ++ "  -l     Generate a BinahLibrary.hs file with data accessor code\n"
usage = "Normal usage is: binah [refined-models]\nTry --help for other options."

flags =
    [ Option ['v'] ["version"] (NoArg Version)
        "Prints the version number."
    , Option ['h'] ["help"] (NoArg Help)
        "Prints the help page."
    , Option ['p'] ["proofs"] (NoArg Proofs)
        "Generates proofs for the models files."
    , Option ['d'] ["decentralized-world"] (NoArg DecentralizedWorld)
        "Generates the decentralized world."
    , Option ['c'] ["centralized-world"] (NoArg CentralizedWorld)
        "Generates the centralized world."
    , Option ['l'] ["library"] (NoArg Library)
        "Generates the BinahLibrary."
    ]

parse argv = case getOpt Permute flags argv of
    ([Version], _, []) -> putStrLn $ "Binah version " ++ version
    ([Help], _, []) -> putStrLn help 
    ([Proofs], [file], []) -> makeProofs file
    ([DecentralizedWorld], [file], []) -> makeDecentralizedWorld file
    ([CentralizedWorld], [file], []) -> makeCentralizedWorld file
    ([], [file], []) -> makeModelsAndSpecFile file
    _ -> putStrLn usage

run :: IO ()
run = do as <- getArgs
         parse as

module ModelsParser where
import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import qualified Data.List.Split as Split
import Data.List
import Data.Char (isSpace)

{- Table Datatype -}
type Var = String
type SimpleType = String

toVar :: String -> Var
toVar x = x

{- Predicate is just a list of strings right now -}
data Type = Refined Var SimpleType [String]
          | Simple SimpleType
          deriving (Show)

data Stmt = NewRecord Var
          | Field Var Type
          | Deriving Var
          deriving (Show)

{- Refined Models Language -}
languageDef =
  emptyDef { Token.commentStart   = ""
           , Token.commentEnd = ""
           , Token.commentLine    = ""
           , Token.nestedComments = True
           , Token.identStart     = letter 
           , Token.identLetter    = alphaNum <|> oneOf "_'"
           , Token.opStart        = alphaNum <|> oneOf "_'" <|> oneOf "!#$%&*+./<=>?@\\^-~"
           , Token.opLetter       = alphaNum <|> oneOf "_'" <|> oneOf "!#$%&*+./<=>?@\\^-~"
           , Token.reservedOpNames= [":", "|"]
           , Token.reservedNames  = ["deriving"]
           , Token.caseSensitive  = True
           }

{- Lexer Helpers -}
lexer = Token.makeTokenParser languageDef
parens = Token.parens lexer
braces = Token.braces lexer
reservedOp = Token.reservedOp lexer
reservedName = Token.reserved lexer
identifier = Token.identifier lexer
whiteSpace = Token.whiteSpace lexer
otherOp = Token.operator lexer
typeOf = Token.colon lexer

{- Helpers for Parsing Refined Types -}
predicateString :: Parser Var
predicateString = otherOp <|> identifier

predicateSequence :: Parser [Var]
predicateSequence = do list <- (many1 predicateString)
                       return list

refinedtype :: Parser Type
refinedtype =
  do var <- identifier
     typeOf
     simptype <- identifier
     reservedOp "|"
     predicate <- predicateSequence
     return $ Refined var simptype predicate

{- Helpers for Parsing Types -}
typ :: Parser Type
typ = (braces refinedtype)
        <|> simpletype 

simpletype :: Parser Type
simpletype = do typ <- many1 identifier
                return $ Simple (intercalate " " typ)
                
{- Helpers for Parsing Derive Statements -}
derive :: Parser Stmt
derive =
  do reservedName "deriving"
     var <- parens identifier <|> identifier
     return $ Deriving var

{- Helpers for Parsing Table and Fields -}
field :: Parser Stmt
field = do var <- identifier
           t <- typ
           return $ Field var t

newtable :: Parser Stmt
newtable = do var <- identifier
              return $ NewRecord var

declaration :: Parser Stmt
declaration = (try field) <|> (try newtable) <|> derive

{- Parsing -}
whileParser :: Parser Stmt
whileParser = whiteSpace >> declaration

parseString :: String -> Stmt
parseString str =
  case parse whileParser "" str of
    Left e  -> error $ show e
    Right r -> r
   
parseExprs :: [String] -> [Stmt]
parseExprs = (map parseString) 

onlyWhitespace :: String -> Bool
onlyWhitespace = null . (dropWhile isSpace)

parseFile :: String -> IO [Stmt]
parseFile file = do program  <- readFile file
                    lines <- return $ filter (not . onlyWhitespace) $ Split.splitOn "\n" program
                    parsed <- return $ parseExprs lines
                    return parsed

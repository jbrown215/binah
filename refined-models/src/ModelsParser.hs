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

data ListType = Id SimpleType
                | Brackets SimpleType
                deriving (Show)


toVar :: String -> Var
toVar x = x

{- Predicate is just a list of strings right now -}
data Type = Refined Var String [String]
          | Simple String
          deriving (Show)

data Stmt = NewRecord Var
          | Field Var Type
          | Deriving Var
          | Blank
          deriving (Show)

{- Refined Models Language -}
languageDef = haskellDef

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
brackets = Token.brackets lexer
integer = Token.integer lexer
stringLit = Token.stringLiteral lexer

{- Helpers for Parsing Refined Types -}

integerString :: Parser Var
integerString = do x <- integer
                   return $ show x

quotedString :: Parser Var
quotedString = do s <- stringLit
                  return $ "\"" ++ s ++ "\""

predicateString :: Parser Var
predicateString = otherOp
                  <|> identifier
                  <|> integerString
                  <|> quotedString

predicateSequence :: Parser [Var]
predicateSequence = do list <- (many1 $ predicateString)
                       return list


listToSimple :: ListType -> SimpleType
listToSimple (Brackets t) = "[" ++ t ++ "]"
listToSimple (Id t) = t

refinedtype :: Parser Type
refinedtype =
  do var <- identifier
     typeOf
     Simple simptype <- simpletype
     reservedOp "|"
     predicate <- predicateSequence
     return $ Refined var simptype predicate

{- Helpers for Parsing Types -}
typ :: Parser Type
typ = (braces refinedtype)
        <|> simpletype

listType :: Parser ListType
listType = do typ <- brackets identifier
              return $ Brackets typ

idType :: Parser ListType
idType = do typ <- identifier
            return $ Id typ

simpletype :: Parser Type
simpletype = do typ <- many1 (idType <|> listType)
                return $ Simple (intercalate " " $ map listToSimple typ)

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
              _ <- eof
              return $ NewRecord var

blank :: Parser Stmt
blank = do _ <- optional $ whiteSpace
           _ <- eof
           return Blank

declaration :: Parser Stmt
declaration = (try field) <|> (try newtable) <|> (try derive) <|> blank

{- Parsing -}
whileParser :: Parser Stmt
whileParser = whiteSpace >> declaration

parseString :: String -> Int -> Stmt
parseString str idx =
  case parse whileParser "" str of
    Left e  -> error $ "Error Line " ++ show idx ++ ": " ++ str ++ "\n" ++ show e
    Right r -> r

mapIdx f l = zipWith f l [1..]

notBlank :: Stmt -> Bool
notBlank Blank = False
notBlank _ = True

parseExprs :: [String] -> [Stmt]
parseExprs = (mapIdx parseString)

onlyWhitespace :: String -> Bool
onlyWhitespace = null . (dropWhile isSpace)

parseFile :: String -> IO [Stmt]
parseFile file = do program  <- readFile file
                    lines <- return $ Split.splitOn "\n" program
                    parsed <- return $ filter notBlank $ parseExprs lines
                    return parsed

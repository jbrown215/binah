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
data OptionalType = Required String
                | Optional String
                deriving Show

toVar :: String -> Var
toVar x = x

{- Predicate is just a list of strings right now -}
data Type = Refined Var OptionalType [String]
          | Simple OptionalType
          deriving (Show)

data TableOptions = TableOptions { json :: Bool,
                                   tableSql :: Maybe String
                                 }
                    deriving Show

data FieldOptions = FieldOptions { fieldSql :: Bool,
                                   sqltype :: Maybe String,
                                   defaultVal :: Maybe String,
                                   migrationOnly :: Bool
                                 }
                    deriving Show

data Stmt = NewRecord Var TableOptions
          | Field Var Type FieldOptions
          | Deriving Var
          | Unique Var Var
          | Blank
          deriving (Show)

{- Helpers for Options -}
defaultTableOpt = TableOptions {json=False,
                                tableSql=Nothing}

defaultFieldOpt = FieldOptions {fieldSql=False,
                                sqltype=Nothing,
                                defaultVal=Nothing,
                                migrationOnly=False}

{- Refined Models Language -}
languageDef = haskellDef

{- Lexer Helpers -}
lexer = Token.makeTokenParser languageDef
parens = Token.parens lexer
braces = Token.braces lexer
reservedOp = Token.reservedOp lexer
reservedName = Token.reserved lexer
ident = Token.identifier lexer
whiteSpace = Token.whiteSpace lexer
otherOp = Token.operator lexer
typeOf = Token.colon lexer
brackets = Token.brackets lexer
integer = Token.integer lexer
stringLit = Token.stringLiteral lexer

{- Identifiers - Reserving Models Keywords -}
identifier = do _ <- notFollowedBy (string "json")
                x <- ident
                return x



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

listType :: Parser String
listType = do typ <- brackets identifier
              return $ "[" ++ typ ++ "]"

idType :: Parser String
idType = do typ <- identifier
            return $ typ


simpletype :: Parser Type
simpletype = do typ <- many1 (idType <|> listType)
                return $ case last typ of
                           "Maybe" -> Simple $ Optional $ intercalate " " $ init typ
                           _ -> Simple $ Required $ intercalate " " typ

{- Helpers for Parsing Derive Statements -}
derive :: Parser Stmt
derive =
  do reservedName "deriving"
     var <- parens identifier <|> identifier
     return $ Deriving var

{- Helpers for Parsing Unique statements-}
uniqueField :: Parser Stmt
uniqueField =
  do string "Unique"
     uniqueName <- identifier
     fieldName <- identifier
     return $ Unique uniqueName fieldName

{- Helpers for Parsing Table and Fields -}
field :: Parser Stmt
field = do var <- identifier
           t <- typ
           return $ Field var t (FieldOptions {fieldSql=False,
                                               sqltype=Nothing,
                                               defaultVal=Nothing,
                                               migrationOnly=False})


newtable :: Parser Stmt
newtable = (try simpletable) <|> opttable

simpletable :: Parser Stmt
simpletable = do var <- identifier
                 _ <- eof
                 return $ NewRecord var (TableOptions {json=False, tableSql=Nothing})

opttable :: Parser Stmt
opttable = do var <- identifier
              _ <- string "json"
              -- TODO: get the sql options
              return $ NewRecord var (TableOptions {json=True, tableSql=Nothing})


blank :: Parser Stmt
blank = do _ <- optional $ whiteSpace
           _ <- eof
           return Blank

declaration :: Parser Stmt
declaration = (try uniqueField) <|> (try field) <|> (try newtable) <|> (try derive) <|> blank

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

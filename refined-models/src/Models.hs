module Models where

{-# LANGUAGE OverloadedStrings #-}
import System.IO
import Control.Monad
import qualified Data.List.Split as Split
import Data.List
import Data.Char (isSpace, toUpper, toLower)
import qualified Data.Set as Set
import ModelsParser

toSimpleType :: Type -> SimpleType
toSimpleType (Simple s) = s
toSimpleType (Refined _ s _) = s


makeRevGroups :: [Stmt] -> [Stmt] -> [[Stmt]]
makeRevGroups [] acc = [acc]
makeRevGroups (x:xs) acc = case x of
                             NewRecord _ -> acc : (makeRevGroups xs [x])
                             Field _ _ -> makeRevGroups xs (x:acc)
                             Deriving _ -> makeRevGroups xs (x:acc)
                             Unique _ _ -> makeRevGroups xs (x:acc)

makeGroups :: [Stmt] -> [[Stmt]]
makeGroups l = filter (not . null) . (map (Data.List.reverse)) $ makeRevGroups l []

prettyPrintStmt :: Stmt -> String
prettyPrintStmt (NewRecord str) = str ++ "\n"
prettyPrintStmt (Field var (Simple typ)) = "   " ++ var ++ " " ++ typ ++ "\n"
prettyPrintStmt (Field var (Refined _ typ _)) = "   " ++  var ++ " " ++ typ ++ "\n"
prettyPrintStmt (Deriving str) = "   deriving " ++ str ++ "\n"
prettyPrintStmt (Unique n f) = "   Unique" ++ n ++ " " ++ f ++ "\n"

firstCapital :: String -> String
firstCapital (s : ss) = toUpper s : ss

sentenceCase :: String -> String
sentenceCase str = firstCapital $ map toLower str

formatRecordEntry :: String -> Stmt -> (String, String) 
formatRecordEntry tableName e =
  case e of
    Field v (Simple t) -> (tableName ++ (firstCapital v) ++ " :: " ++ t,
                           (tableName ++ (firstCapital v)))
    Field v (Refined tv t refinement) ->
      (tableName ++ (firstCapital v) ++ " :: {" ++ tv ++ ":" ++ t ++ " | " ++ (intercalate " " refinement) ++ "}",
        (tableName ++ (firstCapital v)))
      
notDerivingOrUnique :: Stmt -> Bool
notDerivingOrUnique (Deriving _) = False
notDerivingOrUnique (Unique _ _) = False
notDerivingOrUnique _ = True
    
formatTableRecord :: [Stmt] -> (String, Set.Set String)
formatTableRecord (NewRecord tableName : entries) =
  let (formattedEntries, records) = unzip $
                                    map (formatRecordEntry $ map toLower tableName)
                                    (filter notDerivingOrUnique entries) in
  ("{-@\n" ++
  "data " ++
  (sentenceCase tableName) ++
  " = " ++ (sentenceCase tableName) ++ "\n\t{ " ++
  (intercalate "\n\t, " formattedEntries) ++
  "\n\t}" ++
  "\n@-}",
   Set.fromList records)

needsTableName :: Set.Set String -> [String] -> Bool
needsTableName s l = any (\x -> Set.member x s) l

updateRefinement :: Set.Set String -> [String] -> [String]
updateRefinement s l =
  map (\x -> if Set.member x s then x ++ " t" else x) l

formatDataEntry :: Set.Set String -> String -> Stmt -> String 
formatDataEntry entrySet tableName e =
  case e of
    Field v (Simple t) -> "Models." ++ tableName ++ (firstCapital v) ++ " :: " ++ "EntityField " ++ tableName ++ " " ++ t
    Field v (Refined tv t refinement) -> "Models." ++ tableName ++ (firstCapital v) ++ " :: " ++ "EntityField " ++
                                         (if needsTableName entrySet refinement then "t:" ++ tableName
                                         else tableName) ++
                                         " {" ++ tv ++ ":_ | " ++
                                         (intercalate " " (updateRefinement entrySet refinement)) ++ "}"

                                         
formatTableData :: Set.Set String -> [Stmt] -> String
formatTableData entrySet (NewRecord tableName : entries) =
  let entries' = entries ++ [Field "Id" (Refined "v" "" ["True"])] in 
  "{-@\n" ++
  "data EntityField " ++
  (sentenceCase tableName) ++
  " typ where \n   " ++
  (intercalate "\n | " $ map (formatDataEntry entrySet (sentenceCase tableName)) entries')
  ++ "\n@-}"


makeSpecType :: [Stmt] -> String
makeSpecType stmts =
  let (record, entries) = formatTableRecord stmts 
      tableData = (formatTableData entries) . (filter notDerivingOrUnique) $ stmts in
    record ++ "\n\n" ++ tableData

makeSpecFile :: [Stmt] -> String
makeSpecFile stmts = let groups = makeGroups stmts in
                       intercalate "\n\n" $ map makeSpecType groups

makeModelsAndSpecFile :: String -> IO ()
makeModelsAndSpecFile file = do stmts <- parseFile file
                                simpleModels <- return $ concat (map prettyPrintStmt stmts)
                                specs <- return $ makeSpecFile stmts
                                writeFile (file ++ "-simple") simpleModels
                                writeFile (file ++ ".spec") specs
                                return ()

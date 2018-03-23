module Models where

{-# LANGUAGE OverloadedStrings #-}
import System.IO
import Control.Monad
import qualified Data.List.Split as Split
import Data.List
import Data.Char (isSpace, toUpper, toLower)
import qualified Data.Set as Set
import ModelsParser

type SimpleType = String

typToModel :: OptionalType -> String
typToModel (Required s) = s
typToModel (Optional s) = s ++ " Maybe"

toSimpleType :: Type -> SimpleType
toSimpleType (Simple s) = typToModel s
toSimpleType (Refined _ s _) = typToModel s

stringToSimpleType :: String -> SimpleType
stringToSimpleType s = s

makeRevGroups :: [Stmt] -> [Stmt] -> [[Stmt]]
makeRevGroups [] acc = [acc]
makeRevGroups (x:xs) acc = case x of
                             NewRecord _ _ -> acc : (makeRevGroups xs [x])
                             Field _ _ _ -> makeRevGroups xs (x:acc)
                             Deriving _ -> makeRevGroups xs (x:acc)
                             Unique _ _ -> makeRevGroups xs (x:acc)

makeGroups :: [Stmt] -> [[Stmt]]
makeGroups l = filter (not . null) . (map (Data.List.reverse)) $ makeRevGroups l []

toSimpleModel :: Stmt -> String
toSimpleModel (NewRecord str _) = str ++ "\n"
toSimpleModel (Field var (Simple typ) _) = "   " ++ var ++ " " ++ (typToModel typ) ++ "\n"
toSimpleModel (Field var (Refined _ typ _) _) = "   " ++  var ++ " " ++ (typToModel typ) ++ "\n"
toSimpleModel (Deriving str) = "   deriving " ++ str ++ "\n"
toSimpleModel (Unique n f) = "   Unique" ++ n ++ " " ++ f ++ "\n"

firstCapital :: String -> String
firstCapital (s : ss) = toUpper s : ss

sentenceCase :: String -> String
sentenceCase str = firstCapital $ map toLower str

typToHaskell :: OptionalType -> String
typToHaskell (Required s) = s
typToHaskell (Optional s) = "Maybe " ++ s

formatRecordEntry :: String -> Stmt -> (String, String)
formatRecordEntry tableName e =
  case e of
    Field v (Simple t) _ -> (tableName ++ (firstCapital v) ++ " :: " ++ (typToHaskell t),
                           (tableName ++ (firstCapital v)))
    Field v (Refined tv t refinement) _ ->
      (tableName ++ (firstCapital v) ++ " :: {" ++ tv ++ ":" ++ (typToHaskell t) ++ " | " ++ (intercalate " " refinement) ++ "}",
        (tableName ++ (firstCapital v)))

notDerivingOrUnique :: Stmt -> Bool
notDerivingOrUnique (Deriving _) = False
notDerivingOrUnique (Unique _ _) = False
notDerivingOrUnique _ = True

formatTableRecord :: [Stmt] -> (String, Set.Set String)
formatTableRecord (NewRecord tableName _ : entries) =
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
    Field v (Simple t) _ -> "Models." ++ tableName ++ (firstCapital v) ++ " :: " ++ "EntityField " ++ tableName ++ " {v:_ | True}"
    Field v (Refined tv t refinement) _ -> "Models." ++ tableName ++ (firstCapital v) ++ " :: " ++ "EntityField " ++
                                         (if needsTableName entrySet refinement then "t:" ++ tableName
                                         else tableName) ++
                                         " {" ++ tv ++ ":_ | " ++
                                         (intercalate " " (updateRefinement entrySet refinement)) ++ "}"


formatTableData :: Set.Set String -> [Stmt] -> String
formatTableData entrySet (NewRecord tableName _ : entries) =
  let entries' = entries ++ [Field "Id" (Refined "v" (Required "") ["True"]) defaultFieldOpt] in
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
                                simpleModels <- return $ concat (map toSimpleModel stmts)
                                specs <- return $ makeSpecFile stmts
                                writeFile (file ++ "-simple") simpleModels
                                writeFile (file ++ ".spec") specs
                                return ()

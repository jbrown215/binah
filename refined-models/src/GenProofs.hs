module GenProofs where

import ModelsParser
import Models

import Data.Char
import Data.List
import qualified Data.Set as Set

type SimpleTable = (Var, [(Var, SimpleType)])
type RefinedTable = (Var, [(Var, Var, SimpleType, [String])])

data PersistFilter = EQUAL | LE | GE
                     deriving Show
persistFilters = [EQUAL, LE, GE]

toSymbol :: PersistFilter -> String
toSymbol EQUAL = "=="
toSymbol LE    = "<="
toSymbol GE    = ">="

capFirst :: [Char] -> [Char]
capFirst [] = []
capFirst (x:xs) = ((toUpper x):xs)

lowFirst :: [Char] -> [Char]
lowFirst [] = []
lowFirst (x:xs) = ((toLower x):xs)

makeFields :: [Stmt] -> ([(Var, SimpleType)], [Stmt])
makeFields [] = ([], [])
makeFields (x:xs) =
   case x of
    NewRecord _ -> ([], x:xs)
    Deriving _ -> makeFields xs
    Field v t ->
        let (fields, xs') = makeFields xs in
        ((v, toSimpleType t):(fields), xs')

makeRefinedFields :: [Stmt] -> ([(Var, Var, SimpleType, [String])], [Stmt])
makeRefinedFields [] = ([], [])
makeRefinedFields (x:xs) =
    case x of
      NewRecord _ -> ([], x:xs)
      Deriving _ -> makeRefinedFields xs
      Field v (Refined v' t refinements) ->
        let (fields, xs') = makeRefinedFields xs in
        (((v, v', t, refinements)):(fields), xs')
      Field v  (Simple t) ->
        let (fields, xs') = makeRefinedFields xs in
        (((v, toVar "_", t, ["true"])):(fields), xs')

makeRefinedTables :: [Stmt] -> [RefinedTable]
makeRefinedTables [] = []
makeRefinedTables (x:xs) =
    case x of
        NewRecord r ->
            let (fields, xs') = makeRefinedFields xs in
            (r, fields):makeRefinedTables xs'

makeSimpleTables :: [Stmt] -> [SimpleTable]
makeSimpleTables [] = []
makeSimpleTables (x:xs) =
    case x of
        NewRecord r ->
            let (fields, xs') = makeFields xs in
            (r, fields):makeSimpleTables xs'

formatFieldCase :: String -> PersistFilter -> String
formatFieldCase funcName f = funcName ++ " " ++ (show f) ++ " filter given = filter " ++ (toSymbol f) ++ " given" ++ "\n"

formatFieldEval :: Var -> (Var, SimpleType) -> String
formatFieldEval record (field, t) =
    let capField = capFirst field in
    let funcName = "evalQ" ++ record ++ capField in
    let reflectComment = "{-@ reflect " ++ funcName ++ " @-}\n" in
    reflectComment ++ 
    funcName ++ " :: PersistFilter -> " ++ t ++ " -> " ++ t ++ " -> Bool\n" ++
    (concat (map (formatFieldCase funcName) persistFilters)) ++ "\n"

formatCase :: Var -> Var -> String
formatCase record field =
    let capField = capFirst field in
    let lowRecord = lowFirst record in
    "    " ++ record ++ capField ++ " -> evalQ" ++ record ++ capField ++ " (filterFilter filter) (filterValue filter) (" ++ lowRecord ++ capField ++ " x)\n"

formatRecordEval :: SimpleTable -> String
formatRecordEval (record, fields) =
    let fieldEvals = concat $ map (formatFieldEval record) fields in
    let evalRecordSig = "evalQ" ++ record ++ " :: Filter " ++ record ++ " typ -> " ++ record ++ " -> Bool\n" in
    let topCase = "evalQ" ++ record ++ " filter x = case filterField filter of\n" in
    let cases = concat $ map (formatCase record) (map fst fields) in
    let reflectComment = "{-@ reflect evalQ" ++ record ++ " @-}\n" in
    fieldEvals ++ reflectComment ++ evalRecordSig ++ topCase ++ cases ++ "\n\n"

formatDecentralizedWorld :: SimpleTable -> String
formatDecentralizedWorld (name, _) =
    let funcName = "canonical" ++ name in
    let comment = "{-@ reflect " ++ funcName ++ " @-}\n" in
    comment ++ funcName ++ " = undefined\n\n"

makeProofs :: String -> IO ()
makeProofs file = do stmts <- parseFile file
                     let tables = makeSimpleTables stmts
                     putStrLn (concat (map formatRecordEval tables))

makeDecentralizedWorld :: String -> IO ()
makeDecentralizedWorld file =
 do stmts <- parseFile file
    -- let tables = makeSimpleTables stmts
    --putStrLn (concat (map formatDecentralizedWorld tables))
    putStrLn (concat (map makeInvariantsForTable (makeRefinedTables stmts)))

formatCentralizedWorldDataDef :: SimpleTable -> String
formatCentralizedWorldDataDef (table, _) =
    "canonical" ++ table ++ " :: " ++ table ++ "\n"

mapInd :: (a -> Int -> b) -> [a] -> [b]
mapInd f l = zipWith f l [0..]

makeRefinedField tab set (v, v', t, refs) = 
    let capTable = " canonical" ++ (capFirst tab) in
    let refs' = map (\x -> if (x == v') then (v ++ capTable) else x) refs in
    let refs'' = map (\x -> if Set.member x set then x ++ capTable else x) refs' in
    let funcName = (lowFirst tab) ++ "_invariant_" ++ v in
    "{-@ assume " ++ funcName ++ " :: {v:() | " ++ (intercalate " " refs'')++ "} @-}\n"
    ++ funcName ++ " :: ()\n" ++ funcName ++ " = ()\n\n"

makeInvariantsForTable :: RefinedTable -> String
makeInvariantsForTable (t, fs) =
   let fields = Set.fromList (map firstPref fs) in
   let capTable = " canonical" ++ (capFirst t) in
   "{-@ measure" ++ capTable ++ " :: " ++ (capFirst t) ++ " @-}"++ "\n\n" ++ (concat (map (makeRefinedField t fields) fs))  ++ "\n\n" 
   where firstPref (a,_,_,_) = (lowFirst t) ++ (capFirst a)

makeCentralizedWorld :: String -> IO ()
makeCentralizedWorld file =
 do stmts <- parseFile file
    let tables = makeSimpleTables stmts
    putStrLn (concat (map formatDecentralizedWorld tables))
    let whitespace i = if i == 0 then "" else "             , "
    let fields = concat (mapInd (\x i -> (whitespace i) ++ (formatCentralizedWorldDataDef x)) tables)
    let dataWorld =  "data World = { " ++ fields ++
                     "             }\n"
    putStrLn dataWorld 
    let world = "world = World " ++ (concat (map (\(x,_) -> "canonical" ++ x ++ " ") tables)) ++ "\n"
    putStrLn world

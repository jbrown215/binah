module GenProofs where

import ModelsParser
import Models

import Data.Char
import Data.List
import Data.String.Utils
import qualified Data.Set as Set
import Debug.Trace

type SimpleTable = (Var, [(Var, SimpleType, Policy)])
type RefinedTable = (Var, [(Var, Var, SimpleType, [String], Policy)])

data PersistType = TEXT | BSTRING | I64 | DOUBLE | RAT
                 | BOOL | DAY     | TOD | TIME   | LIST
                 | MAYBE

data PersistFilter = EQUAL | LE | GE | LTP | GTP | NE
                     deriving Show

toType :: SimpleType -> PersistType
toType "Text"       = TEXT
toType "String"     = TEXT
toType "ByteString" = BSTRING
toType "Int64"      = I64
toType "Int"        = I64
toType "Double"     = DOUBLE
toType "Rational"   = RAT
toType "Bool"       = BOOL
toType "Day"        = DAY
toType "TimeOfDay"  = TOD
toType "UTCTime"    = TIME
toType x            = if startswith "Maybe" x then MAYBE
                      else I64

dropEnd :: Int -> [a] -> [a]
dropEnd i xs = reverse (drop i (reverse xs))

normalizeType :: SimpleType -> SimpleType
normalizeType t = if endswith "Maybe" t then
                    stringToSimpleType $ "Maybe " ++ (dropEnd 6 t)
                  else
                    t

persistFilters :: PersistType -> [PersistFilter]
persistFilters TEXT    = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters BSTRING = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters I64     = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters DOUBLE  = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters RAT     = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters DAY     = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters TOD     = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters TIME    = [EQUAL, LE, GE, LTP, GTP, NE]
persistFilters BOOL    = [EQUAL, NE]
persistFilters LIST    = [EQUAL, NE]
persistFilters MAYBE   = [EQUAL, NE]

toSymbol :: PersistFilter -> String
toSymbol EQUAL = "=="
toSymbol LE    = "<="
toSymbol GE    = ">="
toSymbol LTP   = "<"
toSymbol GTP   = ">"
toSymbol NE    = "/="

capFirst :: [Char] -> [Char]
capFirst [] = []
capFirst (x:xs) = ((toUpper x):xs)

lowFirst :: [Char] -> [Char]
lowFirst [] = []
lowFirst (x:xs) = ((toLower x):xs)

makeFields :: [Stmt] -> ([(Var, SimpleType, Policy)], [Stmt])
makeFields [] = ([], [])
makeFields (x:xs) =
   case x of
    NewRecord _ _ -> ([], x:xs)
    Deriving _ -> makeFields xs
    Unique _ _ -> makeFields xs
    Field v t p _ ->
        let (fields, xs') = makeFields xs in
        ((v, normalizeType $ toSimpleType t, p):(fields), xs')

makeRefinedFields :: [Stmt] -> ([(Var, Var, SimpleType, [String], Policy)], [Stmt])
makeRefinedFields [] = ([], [])
makeRefinedFields (x:xs) =
    case x of
      Unique _ _ -> makeRefinedFields xs
      NewRecord _ _ -> ([], x:xs)
      Deriving _ -> makeRefinedFields xs
      Field v (Refined v' t refinements) p _ ->
        let (fields, xs') = makeRefinedFields xs in
        (((v, v', normalizeType $ toSimpleType (Simple t), refinements, p)):(fields), xs')
      Field v  (Simple t) p _ ->
        let (fields, xs') = makeRefinedFields xs in
        (((v, toVar "_", normalizeType $ toSimpleType (Simple t), ["true"], p)):(fields), xs')

makeRefinedTables :: [Stmt] -> [RefinedTable]
makeRefinedTables [] = []
makeRefinedTables (x:xs) =
    case x of
        NewRecord r _ ->
            let (fields, xs') = makeRefinedFields xs in
            (r, fields):makeRefinedTables xs'

makeSimpleTables :: [Stmt] -> [SimpleTable]
makeSimpleTables [] = []
makeSimpleTables (x:xs) =
    case x of
        NewRecord r _ ->
            let (fields, xs') = makeFields xs in
            (r, fields):makeSimpleTables xs'

formatFieldCase :: String -> PersistFilter -> String
formatFieldCase funcName f = funcName ++ " " ++ (show f) ++ " filter given = given " ++ (toSymbol f) ++ " filter" ++ "\n"

formatFieldEval :: Var -> (Var, SimpleType, Policy) -> String
formatFieldEval record (field, t, _) =
    let capField = capFirst field in
    let funcName = "evalQ" ++ record ++ capField in
    let reflectComment = "{-@ reflect " ++ funcName ++ " @-}\n" in
    let filters = persistFilters (toType t) in
    reflectComment ++
    funcName ++ " :: RefinedPersistFilter -> " ++ t ++ " -> " ++ t ++ " -> Bool\n" ++
    (concat (map (formatFieldCase funcName) filters)) ++ "\n"

formatCase :: Var -> Var -> String
formatCase record field =
    let capField = capFirst field in
    let lowRecord = lowFirst record in
    "    " ++ record ++ capField ++ " -> evalQ" ++ record ++ capField ++ " (refinedFilterFilter filter) (refinedFilterValue filter) (" ++ lowRecord ++ capField ++ " x)\n"

formatGet :: Var -> (Var, SimpleType, Policy) -> String
formatGet table (field, ty, policy) =
  let t = "(" ++ ty ++ ")" in
  let funcName = "get" ++ (capFirst table) ++ (capFirst field) in
  let tagged = "Tagged" ++ (capFirst table) in
  let refinement = "{-@ " ++ funcName ++ " :: forall <p :: " ++ table ++ " -> User -> Bool, q :: " ++ table ++ " -> User -> Bool>.\n"
                   ++ "    {w :: " ++ table ++ " |- User<q w> <: User<{" ++ policy ++ "}>}\n"
                   ++ "    {w :: " ++ table ++ " |- User<q w> <: User<p w>}\n"
                   ++ "    " ++ tagged ++ "<p> " ++ table ++ " -> " ++ tagged ++ "<q> " ++ t ++ "\n"
                   ++ "@-}\n" in
  let typeSig = funcName ++ " :: " ++ tagged ++ " " ++ table ++ " -> " ++ tagged ++ " " ++ t ++ "\n" in
  let impl = funcName ++ " (" ++ tagged ++ " x) = " ++ tagged ++ " $ " ++ (lowFirst table) ++ (capFirst field) ++ " x" in
  refinement ++ typeSig ++ impl ++ "\n\n"


fst3 (a,b,c) = a

formatRecordEval :: SimpleTable -> String
formatRecordEval (record, fields) =
    let fieldEvals = concat $ map (formatFieldEval record) fields in
    let evalRecordSig = "evalQ" ++ record ++ " :: RefinedFilter " ++ record ++ " typ -> " ++ record ++ " -> Bool\n" in
    let topCase = "evalQ" ++ record ++ " filter x = case refinedFilterField filter of\n" in
    let cases = concat $ map (formatCase record) (map fst3 fields) in
    let cases' = cases ++ "    " ++ record ++ "Id -> False" in
    let reflectComment = "{-@ reflect evalQ" ++ record ++ " @-}\n" in
    let multipleFiltersReflect = "\n\n{-@ reflect evalQs" ++ record ++ " @-}\n" in
    let multipleFiltersSig = "evalQs" ++ record ++ " :: [RefinedFilter " ++ record ++ " typ] -> " ++ record ++ " -> Bool\n" in
    let multipleFiltersBody = "evalQs" ++ record ++ " (f:fs) x = evalQ" ++ record ++ " f x && (evalQs" ++ record ++ " fs x)\n" in
    let multipleFiltersDefault = "evalQs" ++ record ++ " [] _ = True\n" in
    let selectRefinement = "{-@ assume select" ++ record ++ " :: forall <p :: "++ record ++ " -> User -> Bool>. f:[RefinedFilter<p> " ++ record ++ " typ]\n"
                        ++ "                -> [SelectOpt " ++ record ++ "]\n"
                        ++ "                -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged" ++ record ++ "<p> [Entity {v:"
                        ++ record ++ " | evalQs" ++ record ++ " f v}]) @-}\n" in
    let selectSignature = "select" ++ record ++ " :: (PersistEntityBackend " ++ record ++ " ~ BaseBackend backend,\n"
                       ++ "      PersistEntity " ++ record ++ ", Control.Monad.IO.Class.MonadIO m,\n"
                       ++ "      PersistQueryRead backend, PersistField typ) =>\n"
                       ++ "      [RefinedFilter " ++ record ++ " typ]\n"
                       ++ "      -> [SelectOpt " ++ record ++ "]\n"
                       ++ "      -> Control.Monad.Trans.Reader.ReaderT backend m (Tagged" ++ record ++ " [Entity " ++ record ++ "])\n"
    in
    let selectImpl = "select" ++ record ++ " fs ts = selectList (map toPersistentFilter fs) ts >>= return . Tagged" ++ record in
    fieldEvals ++ reflectComment ++ evalRecordSig ++ topCase ++ cases' ++
    multipleFiltersReflect ++ multipleFiltersSig ++ multipleFiltersBody ++
    multipleFiltersDefault ++ "\n" ++
    selectRefinement ++
    selectSignature ++
    selectImpl ++ "\n"

formatFieldFilter :: Var -> (Var, Var, SimpleType, [String], Policy) -> String
formatFieldFilter record (field, tname, t, refinements, p) =
  let refinement = "{-@ filter" ++ (capFirst record) ++ (capFirst field) ++ " :: RefinedPersistFilter -> " in
  -- Combining these on one line makes the GHC compiler freak out. nice.
  let refinementPt2 = if tname == "_" then
                           t
                           ++ " -> RefinedFilter<{" ++ p ++ "}> " ++ (capFirst record)
                           ++ " (" ++ t  ++ ") @-}"
                      else "{" ++ tname ++ ":" ++ t ++ " | " ++ (intercalate " " refinements)
                           ++ "} -> RefinedFilter<{" ++ p ++ "}> " ++ (capFirst record)
                           ++ " (" ++ t  ++ ") @-}" in
  let reflection = "{-@ reflect filter" ++ (capFirst record) ++ (capFirst field) ++ " @-}" in
  let typeSig = "filter" ++ (capFirst record) ++ (capFirst field) ++ " :: RefinedPersistFilter -> "
                ++ t ++ " -> RefinedFilter " ++ (capFirst record) ++ " (" ++ t ++ ")" in
  let impl = "filter" ++ (capFirst record) ++ (capFirst field) ++ " f v = RefinedFilter " ++
             (capFirst record) ++ (capFirst field) ++ " v f" in
  refinement ++ refinementPt2 ++ "\n" ++
  reflection ++ "\n" ++
  typeSig ++ "\n" ++
  impl ++ "\n\n"

formatFilters :: RefinedTable -> String
formatFilters (record,fields) = concat (map (formatFieldFilter record) fields)

formatGets :: SimpleTable -> String
formatGets (record, fields) = concat (map (formatGet record) fields)

makeProofs :: String -> IO ()
makeProofs file = do stmts <- parseFile file
                     let tables = makeSimpleTables stmts
                     let proofs = (concat (map formatRecordEval tables))
                     let filters = (concat (map formatFilters (makeRefinedTables stmts)))
                     let gets = (concat (map formatGets (makeSimpleTables stmts)))
                     putStrLn (proofs ++ "\n" ++ filters ++ "\n" ++ gets)

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
    {-@ data EntityField @-}
    data EntityField record :: * -> *

{-@ data Filter record typ = Filter { filterField :: EntityField record typ, filterValue :: typ, filterFilter :: PersistFilter } @-}
data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    } 

{-@ reflect createEqQuery @-}
createEqQuery :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
createEqQuery field value = Filter field value EQUAL

{-@ reflect createLeQuery @-}
createLeQuery :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> Filter record typ
createLeQuery field value =
  Filter {
    filterField = field
  , filterValue = value
  , filterFilter = LE 
  }

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
    {-@ data EntityField record typ where
        BlobXVal :: EntityField Blob Int
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQBlobXVal @-}
evalQBlobXVal :: PersistFilter -> Int -> Int -> Bool
evalQBlobXVal EQUAL filter given = filter == given
evalQBlobXVal LE filter given = given <= filter
evalQBlobXVal GE filter given = given >= filter

{-@ reflect evalQBlobYVal @-}
evalQBlobYVal :: PersistFilter -> Int -> Int -> Bool
evalQBlobYVal EQUAL filter given = filter == given
evalQBlobYVal LE filter given = given <= filter
evalQBlobYVal GE filter given = given >= filter

{-@ reflect evalQBlob @-}
evalQBlob :: Filter Blob typ -> Blob -> Bool
evalQBlob filter blob = case filterField filter of
    BlobXVal -> evalQBlobXVal (filterFilter filter) (filterValue filter) (xVal blob)
    BlobYVal -> evalQBlobYVal (filterFilter filter) (filterValue filter) (yVal blob)

{-@ filterQBlob :: f:(Filter Blob a) -> [Blob] -> [{b:Blob | evalQBlob f b}] @-}
filterQBlob :: Filter Blob a -> [Blob] -> [Blob]
filterQBlob q = filter (evalQBlob q)

{-@ assume select :: f:(Filter Blob a) -> [{b:Blob | evalQBlob f b}] @-}
select :: Filter Blob a -> [Blob]
select _ = undefined

-- Client code:

-- Should typecheck:
-- Why does only the second one typecheck?
-- {-@ getZeros :: () -> [{b:Blob | xVal b = 0}] @-}
-- getZeros :: () -> [Blob]
-- getZeros () = select (createEqQuery BlobXVal 0)

{-@ getZeros_ :: () -> [{b:Blob | xVal b = 0}] @-}
getZeros_ :: () -> [Blob]
getZeros_ () = select (Filter BlobXVal 0 EQUAL)

{-@ getBiggerThan10 :: () -> [{b:Blob | xVal b >= 10}] @-}
getBiggerThan10 :: () -> [Blob]
getBiggerThan10 () = select (Filter BlobXVal 11 GE)

-- Should not typecheck
{-@ getBiggerThan10Fail :: () -> [{b:Blob | xVal b >= 10}] @-}
getBiggerThan10Fail :: () -> [Blob]
getBiggerThan10Fail () = select (Filter BlobXVal 9 GE)

-- coming up: selectFrom :: Table -> Filter -> Blob
-- finally: selectWhere :: Table -> [Filter] -> Blob! We're almost there!

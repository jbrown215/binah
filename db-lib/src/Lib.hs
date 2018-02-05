{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 
module Lib where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Models

data RefinedPersistFilter = EQUAL | LE | GE

{-@ data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 
@-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 

-- This is problematic because we don't want typ in the signature but we need it for LH
{-@ data RefinedUpdate record typ = RefinedUpdate { refinedUpdateField :: EntityField record typ, refinedUpdateValue :: typ } @-}
data RefinedUpdate record typ = RefinedUpdate 
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ
    } 

{-@ =# :: EntityField record a -> a -> RefinedUpdate record a @-}
(=#) :: PersistField typ => EntityField v typ -> typ -> RefinedUpdate v typ
x =# y = RefinedUpdate x y


{-@ reflect === @-}
(===) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field === value = RefinedFilter field value EQUAL

{-@ reflect <== @-}
(<==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field <== value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LE 
  }

{-@ reflect >== @-}
(>==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field >== value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE 
  }


toPersistentFilter :: PersistField typ =>
                      RefinedFilter record typ -> Filter record
toPersistentFilter filter =
    case refinedFilterFilter filter of
         EQUAL -> (refinedFilterField filter) ==. (refinedFilterValue filter)
         LE -> (refinedFilterField filter) <=. (refinedFilterValue filter)
         GE -> (refinedFilterField filter) >=. (refinedFilterValue filter)

toPersistentUpdate :: PersistField typ =>
                      RefinedUpdate record typ -> Update record
toPersistentUpdate (RefinedUpdate a b) = a =. b

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQBlobXVal @-}
evalQBlobXVal :: RefinedPersistFilter -> Int -> Int -> Bool
evalQBlobXVal EQUAL filter given = filter == given
evalQBlobXVal LE filter given = given <= filter
evalQBlobXVal GE filter given = given >= filter

{-@ reflect evalQBlobYVal @-}
evalQBlobYVal :: RefinedPersistFilter -> Int -> Int -> Bool
evalQBlobYVal EQUAL filter given = filter == given
evalQBlobYVal LE filter given = given <= filter
evalQBlobYVal GE filter given = given >= filter

{-@ reflect evalQBlob @-}
evalQBlob :: RefinedFilter Blob typ -> Blob -> Bool
evalQBlob filter blob = case refinedFilterField filter of
    BlobXVal -> evalQBlobXVal (refinedFilterFilter filter) (refinedFilterValue filter) (blobXVal blob)
    BlobYVal -> evalQBlobYVal (refinedFilterFilter filter) (refinedFilterValue filter) (blobYVal blob)
    BlobId   -> False

{-@ reflect evalQsBlob @-}
evalQsBlob :: [RefinedFilter Blob typ] -> Blob -> Bool
evalQsBlob (f:fs) blob = evalQBlob f blob && (evalQsBlob fs blob)
evalQsBlob [] _ = True

{-@ assume selectBlob :: f:[RefinedFilter Blob typ]
                -> [SelectOpt Blob]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {b:Blob | evalQsBlob f b}] @-}
selectBlob :: (PersistEntityBackend Blob ~ BaseBackend backend,
                 PersistEntity Blob, Control.Monad.IO.Class.MonadIO m,
                 PersistQueryRead backend, PersistField typ) =>
                [RefinedFilter Blob typ]
                -> [SelectOpt Blob]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity Blob]
selectBlob fs ts = selectList (map toPersistentFilter fs) ts

select :: (PersistEntityBackend record ~ BaseBackend backend,
                 PersistEntity record, Control.Monad.IO.Class.MonadIO m,
                 PersistQueryRead backend, PersistField typ) =>
                [RefinedFilter record typ]
                -> [SelectOpt record]
                -> Control.Monad.Trans.Reader.ReaderT
                     backend m [Entity record]
select fs ts = selectList (map toPersistentFilter fs) ts

update_ id us = update id (map toPersistentUpdate us)

{-@ getBiggerThan10 :: () -> ReaderT backend m [Entity {b:Blob | blobXVal b >= 10}] @-}
getBiggerThan10 :: (BaseBackend backend ~ SqlBackend,
                    PersistQueryRead backend, MonadIO m) =>
                   () -> ReaderT backend m [Entity Blob]
getBiggerThan10 () = selectBlob [BlobXVal >== 10] []

someFunc :: IO ()
someFunc = runSqlite ":memory:" $ do
    runMigration migrateAll

    johnId <- insert $ Person "John Doe" $ Just 35
    janeId <- insert $ Person "Jane Doe" Nothing

    insert $ BlogPost "My fr1st p0st" johnId
    insert $ BlogPost "One more for good measure" johnId

    oneJohnPost <- select [BlogPostAuthorId === johnId] [LimitTo 1]
    liftIO $ print (oneJohnPost :: [Entity BlogPost])

    blobs <- getBiggerThan10 ()
    blobId <- insert $ Blob 10 10
    update_ blobId [BlobXVal =# 10]

    let x = map (\a b -> blogPostTitle b) oneJohnPost
    john <- get johnId
    liftIO $ print (john :: Maybe Person)

    delete janeId
    deleteWhere [BlogPostAuthorId ==. johnId]

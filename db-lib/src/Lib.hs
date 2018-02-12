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
import           BinahLibrary

update_ id us = update id (map toPersistentUpdate us)
{-@ getBiggerThan10 :: () -> ReaderT backend m [Entity {b:Blob | blobXVal b >= 10}] @-}
getBiggerThan10 :: (BaseBackend backend ~ SqlBackend,
                    PersistQueryRead backend, MonadIO m) =>
                   () -> ReaderT backend m [Entity Blob]
getBiggerThan10 () = selectBlob [BlobXVal >=# 10] []



someFunc :: IO ()
someFunc = runSqlite ":memory:" $ do
    runMigration migrateAll

    blobs <- getBiggerThan10 ()
    blobId <- insert $ Blob 10 10
	
    update_ blobId [BlobXVal =# 92]

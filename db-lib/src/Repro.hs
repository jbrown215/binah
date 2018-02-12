{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ExistentialQuantification  #-}

{-@ LIQUID "--no-adt"                   @-}
{-@ LIQUID "--exact-data-con"           @-}
{-@ LIQUID "--higherorder"              @-}
{-@ LIQUID "--no-termination"           @-}
{-@ LIQUID "--ple"                      @-} 

module Repro where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Models
import           BinahLibraryRepro

{-@ getEqualTo10 :: () -> ReaderT backend m [Entity {b:Blob | blobXVal b = 10}] @-}
getEqualTo10 :: (BaseBackend backend ~ SqlBackend,
                    PersistQueryRead backend, MonadIO m) =>
                   () -> ReaderT backend m [Entity Blob]
getEqualTo10 () = selectBlob [BlobXVal ==# 10] []

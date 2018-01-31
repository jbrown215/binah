{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

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

data RefinedPersistFilter = EQUAL | LE | GE

data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 

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

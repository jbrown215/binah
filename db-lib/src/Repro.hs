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

{-@ data RefinedUpdate record typ = RefinedUpdate { refinedUpdateField :: EntityField record typ, refinedUpdateValue :: typ } @-}
data RefinedUpdate record typ = RefinedUpdate 
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ
    } 

{-@ (=#) :: EntityField record a -> a -> RefinedUpdate record a @-}
(=#) :: PersistField typ => EntityField v typ -> typ -> RefinedUpdate v typ
x =# y = RefinedUpdate x y

toPersistentUpdate :: PersistField typ =>
                      RefinedUpdate record typ -> Update record
toPersistentUpdate (RefinedUpdate a b) = a =. b

update_ id us = update id (map toPersistentUpdate us)

test () = do
    blobId <- insert $ Blob 10 10
    update_ blobId [BlobXVal =# (-1)]

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

module Models where

import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH

{-@ data EntityField Blob typ where
      Models.BlobXVal :: EntityField Blob {v:_ | True}
    | Models.BlobYVal :: EntityField Blob {v:_ | True}
    | Models.BlobId   :: EntityField Blob {v:_ | True}
  @-}

{-@ assume Prelude.error :: String -> a @-} 

share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Person
    name String
    age Int Maybe
    deriving Show
BlogPost
    title String
    authorId PersonId
    deriving Show
Blob
    ~xVal Int
    ~yVal Int
|]


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

import           Control.Monad
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Data.Aeson
import           Data.HashMap.Strict
import           Data.Int
import           Data.Map
import           Data.Proxy
import           Data.Text
import           Web.Internal.HttpApiData
import           Web.PathPieces

{-@ data EntityField Blob typ where
      Models.BlobXVal :: EntityField Blob {v:_ | v >= 0}
    | Models.BlobYVal :: EntityField Blob {v:_ | True}
    | Models.BlobId   :: EntityField Blob {v:_ | True}
  @-}

{-@ data User = User { userEmail :: String
                     , userPassword :: String
                     , userVerkey :: String
                     , userVerified :: Bool 
                     }
@-}

{-@ data EntityField User typ where
      Models.UserEmail :: EntityField User {v:_ | True} 
    | Models.UserPassword :: EntityField User {v:_ | True}
    | Models.UserVerkey :: EntityField User {v:_ | True}
    | Models.UserVerified :: EntityField User {v:_ | True}
    | Models.UserId :: EntityField User {v:_ | True}
  @-}

{-@ data Blob = Blob { blobXVal :: Int, blobYVal :: Int } @-}

{-@ assume Prelude.error :: String -> a @-} 
share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
User
   ~email [Char]
   ~password [Char]
   ~verkey [Char]
   ~verified Bool
   UniqueUser email
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


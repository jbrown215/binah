{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

module Models where

import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH

{-@ data EntityField Blob typ where
      BlobXVal :: EntityField Blob {v:_ | True}
    | BlobYVal :: EntityField Blob {v:_ | True}
  @-}

{-@ assume error :: String -> a @-} 

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
    xVal Int
    yVal Int
|]


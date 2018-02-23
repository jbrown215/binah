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

{-@ assume Prelude.error :: String -> a @-} 
share [mkPersist sqlSettings, mkMigrate "migrateAll"] [persistLowerCase|
Person
    name String
    UniqueName name
    age Int Maybe
|]

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

{- data EntityField Blob typ where
      BlobXVal :: EntityField Blob {v:_ | True}
    | BlobYVal :: EntityField Blob {v:_ | True}
    | BlobId   :: EntityField Blob {v:_ | True}
  -}

{-@ assume Prelude.error :: String -> a @-} 

{- 
data RefinedPersistFilter = EQUAL | LE | GE

data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 

{-@ reflect evalQBlob @-}
evalQBlob :: RefinedFilter Blob typ -> Blob -> Bool
evalQBlob filter blob = case refinedFilterField filter of
  BlobXVal -> True
  BlobYVal -> True
  BlobId ->   True
	
-}

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


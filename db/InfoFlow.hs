{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs, EmptyDataDecls #-}

module Query where

import Prelude hiding (filter)

data User
data PersistFilter = EQUAL | LE | GE

{-@ data Filter record typ <p :: User -> Bool> = Filter
  {
    filterField :: EntityField<p> record typ
  , filterValue :: typ
  , filterFilter :: PersistFilter
  } 
@-}
data Filter record typ = Filter
    { filterField  :: EntityField record typ
    , filterValue  :: typ
    , filterFilter :: PersistFilter
    } 

class PersistEntity record where
    {-@ data variance EntityField covariant covariant invariant @-}
    data EntityField record :: * -> *

{-@ data Blob  = B { xVal :: Int, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

instance PersistEntity Blob where
    {-@ data EntityField Blob typ <p :: User -> Bool> where
        BlobXVal :: EntityField Blob Int
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

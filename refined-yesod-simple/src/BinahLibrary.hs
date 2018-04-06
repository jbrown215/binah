
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

module BinahLibrary where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Models
import           Data.Text hiding (map, filter)

data RefinedPersistFilter = EQUAL | NE | LE | LTP | GE | GTP

{-@ data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }
  @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }

{-@ data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ } @-}
data RefinedUpdate record typ = RefinedUpdate
    { refinedUpdateField :: EntityField record typ
    , refinedUpdateValue :: typ
    }

(=#) :: EntityField v typ -> typ -> RefinedUpdate v typ
x =# y = RefinedUpdate x y

{-@ reflect ==# @-}
(==#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field ==# value = RefinedFilter field value EQUAL

{-@ reflect /=# @-}
(/=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field /=# value = RefinedFilter field value NE

{-@ reflect <=# @-}
(<=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field <=# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LE
  }

{-@ reflect <# @-}
(<#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field <# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LTP
  }

{-@ reflect >=# @-}
(>=#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field >=# value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE
  }

{-@ reflect ># @-}
(>#) :: (PersistEntity record, Eq typ) =>
                 EntityField record typ -> typ -> RefinedFilter record typ
field ># value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE
  }


toPersistentFilter :: PersistField typ =>
                      RefinedFilter record typ -> Filter record
toPersistentFilter filter =
    case refinedFilterFilter filter of
         EQUAL -> (refinedFilterField filter) ==. (refinedFilterValue filter)
         NE -> (refinedFilterField filter) !=. (refinedFilterValue filter)
         LE -> (refinedFilterField filter) <=. (refinedFilterValue filter)
         LTP -> (refinedFilterField filter) <. (refinedFilterValue filter)
         GE -> (refinedFilterField filter) >=. (refinedFilterValue filter)
         GTP -> (refinedFilterField filter) >. (refinedFilterValue filter)

toPersistentUpdate :: PersistField typ =>
                      RefinedUpdate record typ -> Update record
toPersistentUpdate (RefinedUpdate a b) = a =. b

refinedUpdate id us = update id (map toPersistentUpdate us)

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQPersonNumber @-}
evalQPersonNumber :: RefinedPersistFilter -> Int -> Int -> Bool
evalQPersonNumber EQUAL filter given = given == filter
evalQPersonNumber LE filter given = given <= filter
evalQPersonNumber GE filter given = given >= filter
evalQPersonNumber LTP filter given = given < filter
evalQPersonNumber GTP filter given = given > filter
evalQPersonNumber NE filter given = given /= filter

{-@ reflect evalQPerson @-}
evalQPerson :: RefinedFilter Person typ -> Person -> Bool
evalQPerson filter x = case refinedFilterField filter of
    PersonNumber -> evalQPersonNumber (refinedFilterFilter filter) (refinedFilterValue filter) (personNumber x)
    PersonId -> False

{-@ reflect evalQsPerson @-}
evalQsPerson :: [RefinedFilter Person typ] -> Person -> Bool
evalQsPerson (f:fs) x = evalQPerson f x && (evalQsPerson fs x)
evalQsPerson [] _ = True

{-@ assume selectPerson :: f:[RefinedFilter Person typ]
                -> [SelectOpt Person]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:Person | evalQsPerson f v}] @-}
selectPerson :: (PersistEntityBackend Person ~ BaseBackend backend,
      PersistEntity Person, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter Person typ]
      -> [SelectOpt Person]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity Person]
selectPerson fs ts = selectList (map toPersistentFilter fs) ts

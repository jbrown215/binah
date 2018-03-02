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
{-@ LIQUID "--no-totality"                      @-}
{-@ LIQUID "--ple" @-} 

module BinahLibrary where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Models

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

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []

{-@ reflect evalQUserEmail @-}
evalQUserEmail :: RefinedPersistFilter -> String -> String -> Bool
evalQUserEmail EQUAL filter given = given == filter
evalQUserEmail LE filter given = given <= filter
evalQUserEmail GE filter given = given >= filter
evalQUserEmail LTP filter given = given < filter
evalQUserEmail GTP filter given = given > filter
evalQUserEmail NE filter given = given /= filter

{-@ reflect evalQUserPassword @-}
evalQUserPassword :: RefinedPersistFilter -> String -> String -> Bool
evalQUserPassword EQUAL filter given = given == filter
evalQUserPassword LE filter given = given <= filter
evalQUserPassword GE filter given = given >= filter
evalQUserPassword LTP filter given = given < filter
evalQUserPassword GTP filter given = given > filter
evalQUserPassword NE filter given = given /= filter

{-@ reflect evalQUserVerkey @-}
evalQUserVerkey :: RefinedPersistFilter -> String -> String -> Bool
evalQUserVerkey EQUAL filter given = given == filter
evalQUserVerkey LE filter given = given <= filter
evalQUserVerkey GE filter given = given >= filter
evalQUserVerkey LTP filter given = given < filter
evalQUserVerkey GTP filter given = given > filter
evalQUserVerkey NE filter given = given /= filter

{-@ reflect evalQUserVerified @-}
evalQUserVerified :: RefinedPersistFilter -> Bool -> Bool -> Bool
evalQUserVerified EQUAL filter given = given == filter
evalQUserVerified NE filter given = given /= filter

{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserEmail -> evalQUserEmail (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail x)
    UserPassword -> evalQUserPassword (refinedFilterFilter filter) (refinedFilterValue filter) (userPassword x)
    UserVerkey -> evalQUserVerkey (refinedFilterFilter filter) (refinedFilterValue filter) (userVerkey x)
    UserVerified -> evalQUserVerified (refinedFilterFilter filter) (refinedFilterValue filter) (userVerified x)
    UserId -> False

{-@ reflect evalQsUser @-}
evalQsUser :: [RefinedFilter User typ] -> User -> Bool
evalQsUser (f:fs) x = evalQUser f x && (evalQsUser fs x)
evalQsUser [] _ = True

{-@ assume selectUser :: f:[RefinedFilter User typ]
                -> [SelectOpt User]
                -> Control.Monad.Trans.Reader.ReaderT backend m [Entity {v:User | evalQsUser f v}] @-}
selectUser :: (PersistEntityBackend User ~ BaseBackend backend,
      PersistEntity User, Control.Monad.IO.Class.MonadIO m,
      PersistQueryRead backend, PersistField typ) =>
      [RefinedFilter User typ]
      -> [SelectOpt User]
      -> Control.Monad.Trans.Reader.ReaderT backend m [Entity User]
selectUser fs ts = selectList (map toPersistentFilter fs) ts


refinedUpdate id us = update id (map toPersistentUpdate us)

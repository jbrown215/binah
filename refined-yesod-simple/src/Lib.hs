{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

{-@ LIQUID "--no-adt" 	       @-}
{-@ LIQUID "--exact-data-con"  @-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--no-termination"  @-}
{-@ LIQUID "--ple"             @-} 

module Lib where
import           Prelude hiding (filter)
import           Control.Monad.IO.Class  (liftIO, MonadIO)
import           Control.Monad.Trans.Reader
import           Database.Persist
import           Database.Persist.Sqlite
import           Database.Persist.TH
import           Models
import           BinahLibrary

{-@ getUserX:: x:String -> ReaderT backend m [Entity {u:User | userEmail u == x}] @-}
getUserX :: (BaseBackend backend ~ SqlBackend,
                    PersistQueryRead backend, MonadIO m) =>
                   String -> ReaderT backend m [Entity User]
getUserX x = selectUser [UserEmail ==# x] []

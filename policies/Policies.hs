{-# Language EmptyDataDecls #-}

{-@ LIQUID "--prune-unsorted" @-}

module Policies where

import Control.Monad.Trans.Identity
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Signatures
import Control.Monad.Trans.Class (MonadTrans(lift))
import Data.Functor.Classes
import Data.Functor.Identity

data Paper = Paper Int
data User = User Int
     deriving Eq

{-@ data HandlerT f a <p :: User -> Bool> = HandlerT { runHandlerT :: f a} @-}
{-@ data variance HandlerT covariant covariant contravariant @-}
data HandlerT f a = HandlerT { runHandlerT :: f a }

instance (Functor m) => Functor (HandlerT m) where
    fmap f = mapHandlerT (fmap f)

{-@ measure content :: HandlerT m a -> a @-}
-- I'm having trouble playing with LH and this refinement
{-@
instance (Monad m) => Monad (HandlerT m) where
 assume >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>. 
        x:HandlerT <p> m a
     -> (u:a -> HandlerT <p> m (b <f u>))
     -> HandlerT <p> m (b<f (content x)>); 
 return :: forall <p :: User -> Bool>. a -> HandlerT <p> m a 
@-}
instance (Monad m) => Monad (HandlerT m) where
    return = HandlerT . return
    m >>= k = HandlerT $ runHandlerT . k =<< runHandlerT m


instance (Applicative m) => Applicative (HandlerT m) where
    pure x = HandlerT (pure x)
    (<*>) = lift2HandlerT (<*>)

instance (MonadIO m) => MonadIO (HandlerT m) where
    liftIO = HandlerT . liftIO

instance MonadTrans HandlerT where
    lift = HandlerT

mapHandlerT :: (m a -> n b) -> HandlerT m a -> HandlerT n b
mapHandlerT f = HandlerT . f . runHandlerT

lift2HandlerT ::
    (m a -> n b -> p c) -> HandlerT m a -> HandlerT n b -> HandlerT p c
lift2HandlerT f a b = HandlerT (f (runHandlerT a) (runHandlerT b))

-- Only user 0 should have access to this secret data
{-@ getSecretData :: User -> HandlerT <{\u -> u == User 0}> IO [Char] @-}
getSecretData:: User -> HandlerT IO [Char] 
getSecretData = undefined


{-@ safeShow :: forall <p :: User -> Bool>. (HandlerT <p> IO a) -> User <p> -> [Char] @-}
safeShow :: HandlerT IO a -> User -> [Char]
safeShow private user = undefined

okAccess :: () -> [Char]
okAccess () = safeShow (getSecretData (User 0)) (User 0)

{-
badAccess :: () -> [Char]
badAccess () = safeShow (getSecretData (User 0)) (User 1)
-}

-- Database Queries

-- Things that should be written as joins:
-- Instead of being a regular function, pretend isAuthor accesses the database to determine
-- true or false
{-

This example is of a self-referential policy with a many-to-many relationship.
It is currently broken, since we cannot reference the data we are returning in
policy for the query function (since the abstract refinement on the monad comes
before the type inside the monad).
{-@ measure author :: User -> Paper -> Bool @-}
{-@ assume isAuthor :: u:User 
                    -> p:Paper 
                    -> HandlerT <{\u -> true}> IO {v:Bool | v <=> author u p} @-}
isAuthor :: User -> Paper -> HandlerT IO Bool
isAuthor (User 0) (Paper 0) = return True
isAuthor (User 0) (Paper 1) = return True
isAuthor (User 1) (Paper 1) = return True
isAuthor (User 1) (Paper 2) = return True
isAuthor _ _ = return False 



{-@ measure inList :: a -> [a] -> Bool @-}
{-@ assume member :: Eq a => x:a -> y:[a] -> {v:Bool | v <=> inList x y} @-}
member :: Eq a => a -> [a] -> Bool
member x y = elem x y

-- Only the authors should be allowed to see this information
{-@ getAuthorsForPaper :: p:Paper 
                       -> Identity <{\u -> inList u users}> (users:[{u:User | author u p}])
@-}
-- Pretend this also accesses the database
getAuthorsForPaper :: Paper -> Identity [User]
getAuthorsForPaper p = do
    user0 <- isAuthor (User 0) p
    user1 <- isAuthor (User 1) p
    return $ (if user0 then [User 0] else []) ++ (if user1 then [User 1] else [])

-- You should only be able to view the authors if you are an author -- this is actually
-- an extremely interesting policy. It involves both a database join, and the policy itself
-- references the sensitive value it's guarding! It's important to be able to express this in
-- Liquid Haskell.
viewAuthors :: () -> [Char]
viewAuthors x = safeShow (getAuthorsForPaper (Paper 0)) (User 1)
-}

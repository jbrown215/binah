{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--no-totality"                      @-}
{-@ LIQUID "--no-pattern-inline"                @-}
{-@ LIQUID "--ple" @-} 


module Field
where

import Prelude hiding (sequence, mapM, filter)

{-@ reflect admin @-}
admin = User "" []

{-@ data TaggedUser a <p :: User -> User -> Bool> = TaggedUser { content :: a } @-}
data TaggedUser a = TaggedUser { content :: a }

{-@ data variance TaggedUser covariant contravariant @-}


{-@
data User = User
     { userName :: String
     , userFriends :: [User]
     }
@-}
data User = User { userName :: String, userFriends :: [User] }
    deriving (Eq, Show)


{-@ taggedUser :: TaggedUser<{\u v -> v == admin}> User @-}
taggedUser :: TaggedUser User
taggedUser = TaggedUser admin

{-@ insertTaggedUser :: TaggedUser<{\u v -> v == admin}> User -> () @-}
-- What we insert should be tagged with something at most as strong as the conjunction of all the policies across the columns
insertTaggedUser :: TaggedUser User -> ()
insertTaggedUser u = undefined

test = insertTaggedUser taggedUser

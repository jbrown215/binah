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

{-@ reflect admin1 @-}
admin1 = User []

{-@ reflect admin2 @-}
admin2 = User [User []]

{-@ data TaggedUser a <p :: User -> User -> Bool> = TaggedUser { content :: a } @-}
data TaggedUser a = TaggedUser { content :: a }

data Identity a = Identity { runIdent :: a }

{-@ data variance TaggedUser covariant contravariant @-}

{-@ collapse :: forall a < p :: User -> User -> Bool
                , q :: User -> User -> Bool
                , r :: User -> User -> Bool
                >.
                {w:: User |- User<r w> <: User<p w>}
                {w:: User |- User<r w> <: User<q w>}
                TaggedUser<p> (TaggedUser<q> User) -> TaggedUser<r> User @-}
collapse :: TaggedUser (TaggedUser User) -> TaggedUser User
collapse (TaggedUser (TaggedUser x))= TaggedUser x

{-@
data User = User
     { userFriends :: [User]
     }
@-}
data User = User { userFriends :: [User] }
    deriving (Eq, Show)

{-@ test :: TaggedUser<{\u v -> u == admin1}> (TaggedUser <{\u v -> v == admin2}> User) -> TaggedUser<{\u v -> u == admin1 && v == admin2}> User @-}
test :: TaggedUser (TaggedUser User) -> TaggedUser User
test x = collapse x


{-@ getUserFriends :: forall <p :: User -> User -> Bool, q :: User -> User -> Bool>.
     {w :: User |- User<q w> <: User<{\u v -> v == admin2}> }
     {w :: User |- User<q w> <: User<p w> }
     TaggedUser<p> User -> TaggedUser<q> [User]
@-}
getUserFriends :: TaggedUser User -> TaggedUser [User]
getUserFriends (TaggedUser u) = TaggedUser $ userFriends u


{-@ testGet :: 
     TaggedUser<{\u v -> u == admin1}> User -> TaggedUser<{\u v -> u == admin1 && v == admin2}> [User]
@-}
testGet :: TaggedUser User -> TaggedUser [User]
testGet x = getUserFriends x


select :: User -> Identity User
select = undefined

{-@ assume collapseTagged :: forall a <p :: a -> User -> Bool, q :: a -> User -> Bool, r :: a -> User -> Bool>.
    {w :: a |- User<r w> <: User<p w>}
    {w :: a |- User<r w> <: User<q w>}
    TaggedUser<p> (Identity (TaggedUser<q> a)) -> Identity (TaggedUser<r> a)
@-}
collapseTagged :: TaggedUser (Identity (TaggedUser a)) -> Identity (TaggedUser a)
collapseTagged (TaggedUser x) = x

{-@ testCollapseTagged :: TaggedUser<{\u v -> u == admin1}> (Identity (TaggedUser<{\u v -> v == admin2}> a))
   -> Identity (TaggedUser<{\u v -> u == admin1 && v == admin2}> a)
@-}
testCollapseTagged :: TaggedUser (Identity (TaggedUser a)) -> Identity (TaggedUser a)
testCollapseTagged x = collapseTagged x

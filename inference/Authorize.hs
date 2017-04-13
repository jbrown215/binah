module Authorize where

{-@ LIQUID "--gradual" @-}
{-@ LIQUID "--savequery" @-}
{-# Language EmptyDataDecls #-}

data User = User1 | User2
    deriving Eq
data Paper
data Route = Home | Profile User | EditProfile User | PaperView Paper
data Authorization = Authorized | NotAuthorized

{-@ measure author :: User -> Paper -> Bool @-}
{-@ assume isAuthor :: u:User -> p:Paper -> {v:Bool | v <=> author u p} @-}
isAuthor :: User -> Paper -> Bool
isAuthor u p = undefined

{-@ measure friend :: User -> User -> Bool @-}
{-@ assume isFriend :: u1:User -> u2:User -> {v:Bool | v <=> friend u1 u2} @-}
isFriend :: User -> User -> Bool
isFriend u1 u2 = undefined

{-@ measure loggedIn :: User -> Bool @-}
{-@ assume isLoggedIn :: u:User -> {v:Bool | v <=> loggedIn u} @-}
isLoggedIn :: User -> Bool
isLoggedIn u = undefined

-- It would be nice if LH could infer ?? to be author u p
{-@ isAuthorized :: u:User -> p:Paper -> {v:Authorization | (v == Authorized) <=> ??} @-}
isAuthorized :: User -> Paper -> Authorization
isAuthorized u p = if isAuthor u p then Authorized else NotAuthorized

{-@ measure isHome :: Route -> Bool @-}
isHome Home = True
isHome _ = False

{-@ measure isEditProfile :: Route -> Bool @-}
isEditProfile (EditProfile _u) = True
isEditProfile _ = False

{-@ measure isProfile :: Route -> Bool @-}
isProfile (Profile _u) = True
isProfile _ = False

{-@ measure isPaperView :: Route -> Bool @-}
isPaperView (PaperView _u) = True
isPaperView _ = False

-- Now a bit more general and complicated. I would like to infer the following 4 cases:
-- isLoggedIn u
-- OR
-- r is some Profile u2 and isFriend u u2
-- OR
-- r is some EditProfile u2 and u1 == u2
-- OR
-- r is some PaperView p and isAuthor u p
{-@ isAuthorizedR :: u:User -> r:Route -> {v:Authorization | (Authorized == v) <=> ??} @-}
isAuthorizedR :: User -> Route -> Authorization
isAuthorizedR u Home = if isLoggedIn u then Authorized else NotAuthorized
isAuthorizedR u1 (Profile u2) = if isFriend u1 u2 then Authorized else NotAuthorized
isAuthorizedR u1 (EditProfile u2) = if u1 == u2 then Authorized else NotAuthorized
isAuthorizedR u (PaperView p) = if isAuthor u p then Authorized else NotAuthorized

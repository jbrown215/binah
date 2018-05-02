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
import qualified Data.Set as Set


{-@ reflect admin @-}
admin = User "" []

{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }
  deriving Eq

{-@ data variance Tagged covariant contravariant @-}

data RefinedPersistFilter = EQUAL

{-@ data RefinedFilter record typ <r :: record -> Bool, q :: User -> User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 
  @-}
{-@ data variance RefinedFilter covariant covariant covariant contravariant @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    }
    
{-@
data User = User
     { userName :: String
     , userFriends :: [User]
     }
@-}
data User = User { userName :: String, userFriends :: [User] }
    deriving (Eq, Show)

{-@
data EntityField User typ where 
   Field.UserName :: EntityField User {v:_ | True}
 | Field.UserFriends :: EntityField User {v:_ | True}
@-}
data EntityField a b where
  UserName :: EntityField User String
  UserFriends :: EntityField User [User]

{-@ filterUserName ::
       name: String -> RefinedFilter<{\row -> userName row == name}, {\row v -> friends [row] v}> User String @-}
{-@ reflect filterUserName @-}
filterUserName :: String -> RefinedFilter User String 
filterUserName v = RefinedFilter UserName v EQUAL

{-@ assume selectUser :: forall <r :: User -> Bool, p :: User -> Bool, q :: User -> User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q row> }
                         f: (RefinedFilter<r, q> User typ) -> Tagged<p> [(User<r>)]
@-}
selectUser ::
      RefinedFilter User typ
      -> Tagged [User]
selectUser fs = undefined

{-@ assume Prelude.error :: [Char] -> a @-} 

{-@ measure friends :: [User] -> User -> Bool @-}
{-@ assume isFriends :: forall <p :: User -> Bool>. u:Tagged<p> [User] -> v:Tagged<p> User -> Tagged<p> {b:Bool | b <=> friends (content u) (content v)} @-}
isFriends :: Tagged [User] -> Tagged User -> Tagged Bool
isFriends u v = do
  rows <- u
  viewer <- v
  let bools = map (\x -> elem viewer (userFriends x)) rows
  return $ foldl (&&) True bools 

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
  -- f (a -> b) -> f a -> f b
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >>  t = t
  fail          = error

{-@ instance Monad Tagged where
     >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>.
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>);
     >>  :: x:Tagged a
         -> Tagged b
         -> Tagged b;
     return :: forall <p :: User -> Bool>. a -> Tagged <p> a
  @-}

{-@
downgradeBool :: forall < p :: User -> Bool
                , q :: User -> Bool
                , r :: Bool -> Bool
                >.
       {x:: {v:Bool<r> | v <=> true} |- User<p> <: User<q>}
      x: Tagged <q> (Bool<r>)
    -> Tagged <p> (Bool<r>)
@-}
downgradeBool :: Tagged Bool -> Tagged Bool
downgradeBool (Tagged x) = Tagged x

{- Policy combinators -}

user1 = "user1"
user2 = "user2"

{-@ selectTaggedData1 :: forall <p :: User -> Bool>.
                         { row :: {v:User | userName v == user1} |- User<p> <: {v:User | friends [row] v} }
                         () -> Tagged<p> [{v: User | userName v == user1}]
@-}
selectTaggedData1 :: () -> Tagged [User]
selectTaggedData1 () = selectUser (filterUserName user1)

{-@ selectTaggedData2 :: forall <p :: User -> Bool>.
                         { row :: {v:User | userName v == user2} |- User<p> <: {v:User | friends [row] v} }
                         () -> Tagged<p> [{v: User | userName v == user2}]  @-}
selectTaggedData2 :: () -> Tagged [User]
selectTaggedData2 () = selectUser (filterUserName user2)


-- {-@ output :: viewer:(Tagged<{\u v -> true}> User)
                -- -> msg:Tagged<{\v -> v == content viewer}> a
                -- -> () @-}
-- output :: Tagged User -> Tagged a -> ()
-- output = undefined

{-@ message :: viewer:Tagged <{\v -> true}> User -> 
               Tagged <{\v -> v == content viewer}> [User] @-}
message :: Tagged User -> Tagged [User]
message viewer =
  let users = selectTaggedData1 () in
  let friendsOfUser = do
       us <- users
       let u = head us
       return $ userFriends u in
  -- let out = ifM (isFriends user viewer) friendsOfUser defaultFriends in
  let b = downgradeBool (isFriends users viewer) in
  do
    c <- b
    if c 
      then friendsOfUser
      else return []

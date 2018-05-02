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
admin = User 0 []

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
     { userName :: Int
     , userFriends :: [User]
     }
@-}
data User = User { userName :: Int, userFriends :: [User] }
    deriving (Eq, Show)

{-@
data EntityField User typ where 
   Field.UserName :: EntityField User {v:_ | True}
 | Field.UserFriends :: EntityField User {v:_ | True}
@-}
data EntityField a b where
  UserName :: EntityField User Int
  UserFriends :: EntityField User [User]
  
{-@ measure userByName :: Int -> User @-}  

{-@ filterUserName ::
       name: Int -> RefinedFilter<{\row -> row == userByName name}, {\row v -> friends row v}> User Int @-}
{-@ reflect filterUserName @-}
filterUserName :: Int -> RefinedFilter User Int 
filterUserName v = RefinedFilter UserName v EQUAL

{-@ assume selectUser :: forall <r :: User -> Bool, p :: User -> Bool, q :: User -> User -> Bool>.
                         { row :: User<r> |- User<p> <: User<q row> }
                         f: (RefinedFilter<r, q> User typ) -> Tagged<p> (User<r>)
@-}
selectUser ::
      RefinedFilter User typ
      -> Tagged User
selectUser fs = undefined

{-@ assume Prelude.error :: [Char] -> a @-} 

{-@ measure friends :: User -> User -> Bool @-}
{-@ assume isFriends :: forall <p :: User -> Bool>. u:Tagged<p> User -> v:Tagged<p> User -> Tagged<p> {b:Bool | b <=> friends (content u) (content v)} @-}
isFriends :: Tagged User -> Tagged User -> Tagged Bool
isFriends u v = do
  row <- u
  viewer <- v
  return $ elem viewer (userFriends row)

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
     >>  :: forall <p :: User -> Bool>.
            x:Tagged<{\v -> false}> a
         -> Tagged<p> b
         -> Tagged<p> b;
     return :: a -> Tagged <{\v -> true}> a
  @-}

{-@
downgradeBool :: forall < p :: User -> Bool
                , q :: User -> Bool
                , r :: Bool -> Bool
                >.
       {x:: Bool<r> |- User<p> <: User<q>}
      x: Tagged <q> (Bool<r>)
    -> Tagged <p> (Bool<r>)
@-}
downgradeBool :: Tagged Bool -> Tagged Bool
downgradeBool (Tagged x) = Tagged x

{- Policy combinators -}

user1 = 1
user2 = 2

{-@ selectTaggedData1 :: forall <p :: User -> Bool>.
                         { row :: {v:User | v == userByName user1} |- User<p> <: {v:User | friends row v} }
                         () -> Tagged<p> {v: User | v == userByName user1} 
@-}
-- {-@ selectTaggedData1 :: () -> Tagged<{\v -> friends (userByName user1) v}> {v: User | v == userByName user1} 
-- @-}
selectTaggedData1 :: () -> Tagged User
selectTaggedData1 () = selectUser (filterUserName user1)

{-@ selectTaggedData2 :: forall <p :: User -> Bool>.
                         { row :: {v:User | v == userByName user2} |- User<p> <: {v:User | friends row v} }
                         () -> Tagged<p> {v: User | v == userByName user2}  @-}
selectTaggedData2 :: () -> Tagged User
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
  let user = selectTaggedData1 () in
  let friendsOfUser = user >>= (return . userFriends) in
  -- let out = ifM (isFriends user viewer) friendsOfUser defaultFriends in
  let b = downgradeBool (isFriends user viewer) in
  do
    c <- b
    if c 
      then friendsOfUser
      else return []


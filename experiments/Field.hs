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

data RefinedPersistFilter = EQUAL
{-@ data RefinedFilter record typ <p :: User -> record -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 
  @-}
{-@ data variance RefinedFilter covariant covariant contravariant @-}
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

{-@ filterUserName:: RefinedPersistFilter -> String -> RefinedFilter<{\u v -> friends u v}> User String @-}
{-@ reflect filterUserName @-}
filterUserName :: RefinedPersistFilter -> String -> RefinedFilter User String 
filterUserName f v = RefinedFilter UserName v f

{-@ assume selectUser :: forall <p :: User -> User -> Bool>.
                         f:[RefinedFilter<p> User typ]
                      -> TaggedUser<p> User
@-}
selectUser ::
      [RefinedFilter User typ]
      -> TaggedUser User
selectUser fs = undefined

{-@ assume Prelude.error :: [Char] -> a @-} 

{-@ measure friends :: User -> User -> Bool @-}
{-@ assume isFriends :: forall <p :: User -> User -> Bool>. u:TaggedUser<p> User -> v:TaggedUser<p> User -> TaggedUser<p> {b:Bool | b <=> friends (content u) (content v)} @-}
isFriends :: TaggedUser User -> TaggedUser User -> TaggedUser Bool
isFriends u v = do
  row <- u
  viewer <- v
  return $ elem viewer (userFriends row)

instance Functor TaggedUser where
  fmap f (TaggedUser x) = TaggedUser (f x)

instance Applicative TaggedUser where
  pure  = TaggedUser
  -- f (a -> b) -> f a -> f b
  (TaggedUser f) <*> (TaggedUser x) = TaggedUser (f x)

instance Monad TaggedUser where
  return x = TaggedUser x
  (TaggedUser x) >>= f = f x
  (TaggedUser _) >>  t = t
  fail          = error

{-@ instance Monad TaggedUser where
     >>= :: forall <p :: User-> User -> Bool, f:: a -> b -> Bool>.
            x:TaggedUser <p> a
         -> (u:a -> TaggedUser <p> (b <f u>))
         -> TaggedUser <p> (b<f (content x)>);
     >>  :: x:TaggedUser a
         -> TaggedUser b
         -> TaggedUser b;
     return :: forall <p :: User -> User -> Bool>. a -> TaggedUser <p> a
  @-}

{-@
downgradeBool :: forall < p :: User -> User -> Bool
                , q :: User -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: User, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: TaggedUser <q> (Bool<r>)
    -> TaggedUser <p> (Bool<r>)
@-}
downgradeBool :: TaggedUser Bool -> TaggedUser Bool
downgradeBool (TaggedUser x) = TaggedUser x

{- Policy combinators -}

{-@ selectTaggedData1 :: () -> TaggedUser<{\u v -> friends u v}> User @-}
selectTaggedData1 :: () -> TaggedUser User
selectTaggedData1 () = selectUser [filterUserName EQUAL "user1"]

{-@ selectTaggedData2 :: () -> TaggedUser<{\u v -> friends u v}> User @-}
selectTaggedData2 :: () -> TaggedUser User
selectTaggedData2 () = selectUser [filterUserName EQUAL "user2"]


-- Notice that output takes a row so that we can make sure the policy
-- held for that row
{-@ output ::
             row:TaggedUser<{\u v -> false}> User
          -> viewer:(TaggedUser<{\u v -> true}> User)
          -> msg:TaggedUser<{\u v -> v == content viewer && u == content row}> a
          -> () @-}
output :: TaggedUser User -> TaggedUser User -> TaggedUser a -> ()
output = undefined

-- This policy needs to be parameterized by another user, since it
-- actually depends on two users and not just one!
-- i.e., there is no row we can pass in to make sure the
-- policy passes for both
{-@ bad :: () -> TaggedUser<{\u v -> friends u v}> Bool @-}
bad :: () -> TaggedUser Bool
bad =
  let data1 = selectTaggedData1 () in
  let data2 = selectTaggedData2 () in
  do
    u1 <- data1
    u2 <- data2
    return $ data1 == data2

{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--no-totality"                      @-}
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

{-@ filterUserName:: RefinedPersistFilter -> String -> RefinedFilter<{\v u -> friends u v}> User String @-}
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

{-@
ifM :: forall a < p :: User -> User -> Bool
                , q :: User -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: User, c:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
       cond: TaggedUser <q> (Bool<r>)
    -> thn:  TaggedUser <q> a
    -> els:  TaggedUser <p> a
    -> TaggedUser <p> a
@-}
ifM :: TaggedUser Bool -> TaggedUser a -> TaggedUser a -> TaggedUser a
ifM cond thn els
    = downgradeBool cond >>= \c -> if c then thn else els

-- Why is this line needed to type check?
{-@ selectTaggedData :: () -> TaggedUser<{\v u -> friends u v}> User @-}
selectTaggedData :: () -> TaggedUser User
selectTaggedData () = selectUser [filterUserName EQUAL "friend"]

{-@ output :: forall <p :: User -> User -> Bool>.
             row:TaggedUser<p> User
          -> viewer:TaggedUser <p> (User<p row>)
          -> msg:TaggedUser <p> a 
          -> () @-}
output :: TaggedUser User -> TaggedUser User -> TaggedUser a -> ()
output = undefined

{-@ defaultFriends :: TaggedUser <{\v u -> true}> [User] @-}
defaultFriends :: TaggedUser [User]
defaultFriends = return []

sink viewer =
  let user = selectTaggedData () in
  let friendsOfUser = do
       u <- user
       return $ userFriends u in
  let out = ifM (isFriends user viewer) friendsOfUser defaultFriends in
  output user viewer out

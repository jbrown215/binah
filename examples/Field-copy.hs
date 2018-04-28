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

{-@ data Tagged a b <p :: User -> User -> Bool> = Tagged { content :: b } @-}
data Tagged a  b = Tagged { content :: b }

{-@ data variance Tagged covariant covariant contravariant @-}

data RefinedPersistFilter = EQUAL
{-@ data RefinedFilter record typ <p :: record -> User -> Bool> = RefinedFilter
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
                      -> Tagged<p> User User
@-}
selectUser ::
      [RefinedFilter User typ]
      -> Tagged User User
selectUser fs = undefined

{-@ assume Prelude.error :: [Char] -> a @-} 

{-@ measure friends :: User -> User -> Bool @-}
{-@ assume isFriends :: forall <p :: User -> User -> Bool>. u:Tagged<p> User User -> v:Tagged<p> User User -> Tagged<p> User {b:Bool | b <=> friends (content u) (content v)} @-}
isFriends :: Tagged User User -> Tagged User User -> Tagged User Bool
isFriends u v = do
  row <- u
  viewer <- v
  return $ elem viewer (userFriends row)

instance Functor (Tagged a) where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative (Tagged a) where
  pure  = Tagged
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad (Tagged a) where
  return x = Tagged x
  (Tagged x) >>= f = f x
  (Tagged _) >>  t = t
  fail          = error

{-@ instance Monad (Tagged a) where
     >>= :: forall <p :: a -> User -> Bool, f:: b -> c -> Bool>.
            x:Tagged <p> a b
         -> (u:b -> Tagged <p> a (c <f u>))
         -> Tagged <p> a (c<f (content x)>);
     >>  :: x:Tagged a b
         -> Tagged a c
         -> Tagged a c;
     return :: forall <p :: a -> User -> Bool>. b -> Tagged<p> a b
  @-}

{-@
downgradeBool :: forall < p :: a -> User -> Bool
                , q :: User -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: User, x:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
      x: Tagged<q> a (Bool<r>)
    -> Tagged<p> a (Bool<r>)
@-}
downgradeBool :: Tagged a Bool -> Tagged a Bool
downgradeBool (Tagged x) = Tagged x

{- Policy combinators -}

{-@
ifM :: forall a < p :: a -> User -> Bool
                , q :: a -> User -> Bool
                , r :: Bool -> Bool
                >.
       {w:: User, c:: {v:Bool<r> | v <=> true} |- User<p w> <: User<q w>}
       cond: Tagged <q> a (Bool<r>)
    -> thn:  Tagged<q> a b
    -> els:  Tagged<p> a b
    -> Tagged<p> a b
@-}
ifM :: Tagged a Bool -> Tagged a b -> Tagged a b -> Tagged a b
ifM cond thn els
    = downgradeBool cond >>= \c -> if c then thn else els

-- Why is this line needed to type check?
{-@ selectTaggedData :: () -> Tagged<{\u v -> friends u v}> User User @-}
selectTaggedData :: () -> Tagged User User
selectTaggedData () = selectUser [filterUserName EQUAL "friend"]


{-@ testOutput :: forall <p :: a -> User -> Bool>.
             row:Tagged<{\u v -> false}> a a
          -> viewer:(Tagged<p> a User)
          -> msg:Tagged<p> a b 
          -> untaggedRow:a
          -> untaggedViewer:User<p untaggedRow>
          -> () @-}
testOutput :: Tagged a a -> Tagged a User -> Tagged a b -> a -> User -> ()
testOutput = undefined

{-@ defaultFriends :: Tagged<{\u v -> true}> User [User] @-}
defaultFriends :: Tagged User [User]
defaultFriends = return []

{-@ message :: viewer:Tagged<{\u v -> true}> User User -> 
               user:Tagged<{\u v -> friends u v}> User User ->
               Tagged<{\u v -> v == content viewer && u == content user}> User [User] @-}
message :: Tagged User User -> Tagged User User -> Tagged User [User]
message viewer user =
  let friendsOfUser = do
       u <- user
       return $ userFriends u in
  let b = downgradeBool (isFriends user viewer) in
  do
    c <- b
    if c 
      then friendsOfUser
      else defaultFriends

sink :: Tagged User User -> Tagged User User -> ()
sink viewer viewer2 =
  let user = selectTaggedData () in
  let out2 = message viewer2 user in
  let friendsOfUser = do u <- user
                         return $ userFriends u in
  let b = isFriends user viewer in
  let b' = downgradeBool b in
  let out = do
              c <- b'
              if c 
                then friendsOfUser
                else defaultFriends in
                    ()

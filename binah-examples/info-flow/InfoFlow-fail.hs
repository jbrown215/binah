{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--no-pattern-inline"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}


-- Running liquid on this file will verify the queries in
-- the section beginning with the comment "Query Tests"

module InfoFlow where
import Prelude hiding (filter)

-- Tagged Library
{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }

{-@ data variance Tagged covariant contravariant @-}

instance Functor Tagged where
    fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
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

-- Binah generated refinements
-- In a Yesod project, these go in the same file
-- that invokes the Template Haskell code generation
{-@
data User = User
	{ userAge :: {v:Int | v > 0}
	, userEmail :: {v:[Char] | len v > 6}
	, userPassword :: {v:[Char] | len v > 6}
	}
@-}

{-@
data EntityField User typ where 
   InfoFlow.UserAge :: EntityField User {v:_ | v > 0}
 | InfoFlow.UserEmail :: EntityField User {v:_ | len v > 6}
 | InfoFlow.UserPassword :: EntityField User {v:_ | len v > 6}
@-}

-- Yesod persistent data types and functions
data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
    data EntityField record :: * -> *

-- Binah Library
-- In a Yesod project, this should go in its own file

{-@ data RefinedFilter record typ <p :: User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: PersistFilter
    }
  @-}
{-@ data variance RefinedFilter covariant covariant contravariant @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: PersistFilter
    }

{-@ filterUserEmail:: PersistFilter
                   -> email:{v:String | len v > 6}
                   -> RefinedFilter<{\u -> true}> User String
@-}
{-@ reflect filterUserEmail @-}
filterUserEmail :: PersistFilter -> String -> RefinedFilter User String
filterUserEmail f v = RefinedFilter UserEmail v f

{-@ filterUserPassword :: PersistFilter
                   -> {v:String | len v > 6}
                   -> RefinedFilter<{\u -> u == admin}> User String
@-}
{-@ reflect filterUserPassword @-}
filterUserPassword :: PersistFilter -> String -> RefinedFilter User String
filterUserPassword f v = RefinedFilter UserPassword v f


{-@ safeShow :: forall <p :: User -> Bool>.
                Tagged<p> a -> User<p> -> String @-}
safeShow :: Tagged a -> User -> String
safeShow = undefined

{-@ assume collapseTagged :: forall <p :: User -> Bool, q :: User -> Bool, r :: User -> Bool>.
    {w :: a |- User<r> <: User<p>}
    {w :: a |- User<r> <: User<q>}
    Tagged<p> (Tagged<q> a) -> Tagged<r> a
@-}
collapseTagged :: Tagged (Tagged a) -> Tagged a
collapseTagged (Tagged x) = x


{-@ getUserAge :: forall <p :: User -> Bool, q :: User -> Bool>.
    {User<q> <: User<{\u -> true}>}
    {User<q> <: User<p>}
    Tagged<p> User -> Tagged<q> (Int)
@-}
getUserAge :: Tagged User -> Tagged (Int)
getUserAge (Tagged x) = Tagged $ userAge x

{-@ getUserEmail :: forall <p :: User -> Bool, q :: User -> Bool>.
    {User<q> <: User<{\u -> true}>}
    {User<q> <: User<p>}
    Tagged<p> User -> Tagged<q> ([Char])
@-}
getUserEmail :: Tagged User -> Tagged ([Char])
getUserEmail (Tagged x) = Tagged $ userEmail x

{-@ getUserPassword :: forall <p :: User -> Bool, q :: User -> Bool>.
    {User<q> <: User<{\u -> u == admin}>}
    {User<q> <: User<p>}
    Tagged<p> User -> Tagged<q> ([Char])
@-}
getUserPassword :: Tagged User -> Tagged ([Char])
getUserPassword (Tagged x) = Tagged $ userPassword x

-- Template haskell generated code

data User = User
  { userAge      :: Int
  , userEmail    :: [Char]
  , userPassword :: [Char]
  }
  deriving (Eq)

instance PersistEntity User where
    data EntityField User typ where
        UserAge      :: EntityField User Int
        UserEmail    :: EntityField User [Char]
        UserPassword :: EntityField User [Char]

-- Binah generated code from `binah -p`
{-@ reflect evalQUserAge @-}
evalQUserAge :: PersistFilter -> Int -> Int -> Bool
evalQUserAge EQUAL filter given = given == filter
evalQUserAge LE filter given = given <= filter
evalQUserAge GE filter given = given >= filter

{-@ reflect evalQUserEmail @-}
evalQUserEmail :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail EQUAL filter given = given == filter
evalQUserEmail LE filter given = given <= filter
evalQUserEmail GE filter given = given >= filter

{-@ reflect evalQUserPassword @-}
evalQUserPassword :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserPassword EQUAL filter given = given == filter
evalQUserPassword LE filter given = given <= filter
evalQUserPassword GE filter given = given >= filter

{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserAge -> evalQUserAge (refinedFilterFilter filter) (refinedFilterValue filter) (userAge x)
    UserEmail -> evalQUserEmail (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail x)
    UserPassword -> evalQUserPassword (refinedFilterFilter filter) (refinedFilterValue filter) (userPassword x)

{-@ reflect evalQsUser @-}
evalQsUser :: [RefinedFilter User typ] -> User -> Bool
evalQsUser (f:fs) x = evalQUser f x && (evalQsUser fs x)
evalQsUser [] _ = True

{-@ assume selectUser :: forall <p :: User -> Bool>.
                   f:[RefinedFilter<p> User typ]
                -> Tagged<p> {v:User | evalQsUser f v} @-}
selectUser :: [RefinedFilter User typ]
      -> Tagged User
selectUser fs = undefined 

-- Query Tests 

admin = User 50 "JordanB" "1234567"

-- Even though email is public, you must be the admin to view
-- the user's name because the filter was by password.
-- Here, we've simplified the code to just return one record per
-- query
testImplicitFlow :: User -> [Char]
testImplicitFlow u =
  let user = selectUser [filterUserPassword EQUAL "alskdjfaja"] in
  safeShow (getUserEmail user) u

-- Can't view a private field of a public record unless you
-- pass the policy!
testInvalidFlow :: User -> [Char]
testInvalidFlow u =
  let user = selectUser [filterUserEmail EQUAL "test@gmail.com"] in
  -- Safe because the filter used to get the data was public and
  -- the field being accessed is public, too!
  safeShow (getUserPassword user) u


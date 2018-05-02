{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-@ infixr === @-}
{-@ infixr >== @-}
{-@ infixr <== @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}


-- Running liquid on this file will verify the queries in
-- the section beginning with the comment "Query Tests"

module Invariants where
import Prelude hiding (filter)

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
   Invariants.UserAge :: EntityField User {v:_ | v > 0}
 | Invariants.UserEmail :: EntityField User {v:_ | len v > 6}
 | Invariants.UserPassword :: EntityField User {v:_ | len v > 6}
@-}

-- Yesod persistent data types and functions
data PersistFilter = EQUAL | LE | GE

class PersistEntity record where
    data EntityField record :: * -> *

-- Binah Library
-- In a Yesod project, this should go in its own file

{-@ data RefinedFilter record typ = RefinedFilter
   { refinedFilterField :: EntityField record typ
   , refinedFilterValue :: typ
   , refinedFilterFilter:: PersistFilter
   } 
@-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: PersistFilter
    } 


{-@ reflect === @-}
(===) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field === value = RefinedFilter field value EQUAL

{-@ reflect <== @-}
(<==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field <== value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = LE 
  }

{-@ reflect >== @-}
(>==) :: (PersistEntity record, Eq typ) => 
                 EntityField record typ -> typ -> RefinedFilter record typ
field >== value =
  RefinedFilter {
    refinedFilterField = field
  , refinedFilterValue = value
  , refinedFilterFilter = GE 
  }

-- Template haskell generated code

data User = User
  { userAge      :: Int
  , userEmail    :: [Char]
  , userPassword :: [Char]
  }

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

{-@ assume selectUser :: f:[RefinedFilter User typ]
                -> [{v:User | evalQsUser f v}] @-}
selectUser :: [RefinedFilter User typ]
      -> [User]
selectUser fs = undefined 

-- Query Tests 

{-@ selectUsersOver42 :: () -> [{u:User | userAge u >= 42}] @-}
selectUsersOver42 :: () -> [User]
selectUsersOver42 () = selectUser [UserAge >== 42]

{-@ selectUsersWithEmail :: email:{v:[Char] | len v > 6} -> [{u:User | userEmail u == email}] @-}
selectUsersWithEmail :: [Char] -> [User]
selectUsersWithEmail e = selectUser [UserEmail === e]

{-@ selectUsersWithEmailPassword :: 
      email:{v:[Char] | len v > 6}
   -> password:{v:[Char] | len v > 6}
   -> [{v:User | userEmail v == email && userPassword v == password}]
@-}
selectUsersWithEmailPassword :: [Char] -> [Char] -> [User]
selectUsersWithEmailPassword email pass =
    selectUser [UserEmail === email, UserPassword === pass]

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
	{ userEmail1 :: {v:[Char] | len v > 6}
	, userEmail2 :: {v:[Char] | len v > 6}
	, userEmail3 :: {v:[Char] | len v > 6}
	, userEmail4 :: {v:[Char] | len v > 6}
	, userEmail5 :: {v:[Char] | len v > 6}
	}
@-}

{-@
data EntityField User typ where 
   Invariants.UserEmail1 :: EntityField User {v:_ | len v > 6}
 | Invariants.UserEmail2 :: EntityField User {v:_ | len v > 6}
 | Invariants.UserEmail3 :: EntityField User {v:_ | len v > 6}
 | Invariants.UserEmail4 :: EntityField User {v:_ | len v > 6}
 | Invariants.UserEmail5 :: EntityField User {v:_ | len v > 6}
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
  { userEmail1    :: [Char]
  , userEmail2    :: [Char]
  , userEmail3    :: [Char]
  , userEmail4    :: [Char]
  , userEmail5    :: [Char]
  }

instance PersistEntity User where
    data EntityField User typ where
        UserEmail1    :: EntityField User [Char]
        UserEmail2    :: EntityField User [Char]
        UserEmail3    :: EntityField User [Char]
        UserEmail4    :: EntityField User [Char]
        UserEmail5    :: EntityField User [Char]

-- Binah generated code from `binah -p`
{-@ reflect evalQUserEmail1 @-}
evalQUserEmail1 :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail1 EQUAL filter given = given == filter
evalQUserEmail1 LE filter given = given <= filter
evalQUserEmail1 GE filter given = given >= filter

{-@ reflect evalQUserEmail2 @-}
evalQUserEmail2 :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail2 EQUAL filter given = given == filter
evalQUserEmail2 LE filter given = given <= filter
evalQUserEmail2 GE filter given = given >= filter

{-@ reflect evalQUserEmail3 @-}
evalQUserEmail3 :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail3 EQUAL filter given = given == filter
evalQUserEmail3 LE filter given = given <= filter
evalQUserEmail3 GE filter given = given >= filter

{-@ reflect evalQUserEmail4 @-}
evalQUserEmail4 :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail4 EQUAL filter given = given == filter
evalQUserEmail4 LE filter given = given <= filter
evalQUserEmail4 GE filter given = given >= filter

{-@ reflect evalQUserEmail5 @-}
evalQUserEmail5 :: PersistFilter -> [Char] -> [Char] -> Bool
evalQUserEmail5 EQUAL filter given = given == filter
evalQUserEmail5 LE filter given = given <= filter
evalQUserEmail5 GE filter given = given >= filter


{-@ reflect evalQUser @-}
evalQUser :: RefinedFilter User typ -> User -> Bool
evalQUser filter x = case refinedFilterField filter of
    UserEmail1 -> evalQUserEmail1 (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail1 x)
    UserEmail2 -> evalQUserEmail2 (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail2 x)
    UserEmail3 -> evalQUserEmail3 (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail3 x)
    UserEmail4 -> evalQUserEmail4 (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail4 x)
    UserEmail5 -> evalQUserEmail5 (refinedFilterFilter filter) (refinedFilterValue filter) (userEmail5 x)

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

{-@ selectUsersWithEmail :: 
      email:{v:[Char] | len v > 6}
   -> [{v:User | userEmail1 v == email && (userEmail2 v == email) && userEmail3 v == email && userEmail4 v == email && userEmail5 v == email
    }]
@-}
selectUsersWithEmail :: [Char] -> [User]
selectUsersWithEmail email =
    selectUser [ UserEmail1 === email
               , UserEmail2 === email
               , UserEmail3 === email
               , UserEmail4 === email
               , UserEmail5 === email
               ]

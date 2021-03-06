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
data User = User
  { userEmail1    :: [Char]
  , userEmail2    :: [Char]
  , userEmail3    :: [Char]
  , userEmail4    :: [Char]
  , userEmail5    :: [Char]
  }

-- Constructor Tests 

user1 = User "testing" "testing2" "testing3" "testing4" "testing5"
user2 = User "testing" "testing2" "testing3" "testing4" "testing5"
user3 = User "testing" "testing2" "testing3" "testing4" "testing5"
user4 = User "testing" "testing2" "testing3" "testing4" "testing5"
user5 = User "testing" "testing2" "testing3" "testing4" "testing5"
user6 = User "testing" "testing2" "testing3" "testing4" "testing5"
user7 = User "testing" "testing2" "testing3" "testing4" "testing5"
user8 = User "testing" "testing2" "testing3" "testing4" "testing5"
user9 = User "testing" "testing2" "testing3" "testing4" "testing5"
user10 = User "testing" "testing2" "testing3" "testing4" "testing5"
user11 = User "testing" "testing2" "testing3" "testing4" "testing5"
user12 = User "testing" "testing2" "testing3" "testing4" "testing5"
user13 = User "testing" "testing2" "testing3" "testing4" "testing5"
user14 = User "testing" "testing2" "testing3" "testing4" "testing5"
user15 = User "testing" "testing2" "testing3" "testing4" "testing5"
user16 = User "testing" "testing2" "testing3" "testing4" "testing5"
user17 = User "testing" "testing2" "testing3" "testing4" "testing5"
user18 = User "testing" "testing2" "testing3" "testing4" "testing5"
user19 = User "testing" "testing2" "testing3" "testing4" "testing5"
user20 = User "testing" "testing2" "testing3" "testing4" "testing5"

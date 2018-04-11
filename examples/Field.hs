{-# LANGUAGE EmptyDataDecls, GADTs, ExistentialQuantification #-}

{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--no-totality"                      @-}
{-@ LIQUID "--ple" @-} 


module Field (
  EntityField (..),
  admin
  -- set
) where

import Prelude hiding (sequence, mapM)
-- import qualified Data.Set as Set

data User = User Integer
  deriving (Show, Eq)

{-@ reflect admin @-}
admin = User 0

{-@ data Tagged a <p :: User -> Bool> = Tagged { content :: a } @-}
data Tagged a = Tagged { content :: a }



{-@ data variance Tagged covariant contravariant @-}

{-@ output :: forall <p :: User -> Bool>.
             msg:Tagged <p> a 
          -> User<p>
          -> ()
@-}
output :: Tagged a -> User -> ()
output = undefined

data CreditCard = CreditCard { creditCardNumber :: String, creditCardHolder :: String}

-- Note: this does not successfully attach the abstract refinement
{-@ data EntityField a b <p :: User -> Bool> where
    Field.CreditCardNumber :: EntityField <{\u -> False}> CreditCard {v:_ | True} 
  | Field.CreditCardHolder :: EntityField <{\u -> False}> CreditCard {v: _ | True} 
@-}
{-@ assume Prelude.error :: String -> a @-} 
data EntityField a b where
  CreditCardNumber :: EntityField CreditCard String
  CreditCardHolder :: EntityField CreditCard String

data PersistFilter = EQUAL | NEQ

{-@ data Filter a typ <p :: User -> Bool> = Filter { filterFilter :: PersistFilter, filterField :: EntityField <p> a typ, filterValue :: typ } @-}
data Filter a typ =  Filter { filterFilter :: PersistFilter, filterField :: EntityField a typ, filterValue :: typ }
{-@ data variance Filter covariant covariant contravariant @-}

{-@ testFilter :: Filter <{\u -> u == admin}> CreditCard String @-}
testFilter = Filter EQUAL CreditCardHolder ""

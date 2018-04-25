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

data RefinedPersistFilter = EQUAL
{-@ data RefinedFilter record typ <p :: User -> Bool> = RefinedFilter
    { refinedFilterField  :: EntityField<p> record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 
  @-}
data RefinedFilter record typ = RefinedFilter
    { refinedFilterField  :: EntityField record typ
    , refinedFilterValue  :: typ
    , refinedFilterFilter :: RefinedPersistFilter
    } 

{-@ filter :: f:(a -> Bool) -> [a] -> [{v:a | f v}] @-}
filter :: (a -> Bool) -> [a] -> [a]
filter f (x:xs)
  | f x         = x : filter f xs
  | otherwise   =     filter f xs
filter _ []     = []


{-@ reflect evalQCreditCardNumber @-}
evalQCreditCardNumber :: RefinedPersistFilter -> Int -> Int -> Bool
evalQCreditCardNumber EQUAL filter given = given == filter

{-@ reflect evalQCreditCardHolder @-}
evalQCreditCardHolder :: RefinedPersistFilter -> [Char] -> [Char] -> Bool
evalQCreditCardHolder EQUAL filter given = given == filter

{-@ reflect evalQCreditCard @-}
evalQCreditCard :: RefinedFilter CreditCard typ -> CreditCard -> Bool
evalQCreditCard filter x = case refinedFilterField filter of
    CreditCardNumber -> evalQCreditCardNumber (refinedFilterFilter filter) (refinedFilterValue filter) (creditCardNumber x)
    CreditCardHolder -> evalQCreditCardHolder (refinedFilterFilter filter) (refinedFilterValue filter) (creditCardHolder x)

{-@ reflect evalQsCreditCard @-}
evalQsCreditCard :: [RefinedFilter CreditCard typ] -> CreditCard -> Bool
evalQsCreditCard (f:fs) x = evalQCreditCard f x && (evalQsCreditCard fs x)
evalQsCreditCard [] _ = True

{-@ assume selectCreditCard :: f:[RefinedFilter CreditCard typ]
                -> Tagged [{v:CreditCard | evalQsCreditCard f v}] @-}
selectCreditCard ::
      [RefinedFilter CreditCard typ]
      -> Tagged [CreditCard]
selectCreditCard fs = undefined

{-@ filterCreditCardNumber :: RefinedPersistFilter -> Int -> RefinedFilter<{\u -> u == admin}> CreditCard Int @-}
filterCreditCardNumber :: RefinedPersistFilter -> Int -> RefinedFilter CreditCard Int
filterCreditCardNumber f v = RefinedFilter CreditCardNumber v f

{-@ filterCreditCardHolder :: RefinedPersistFilter -> [Char] -> RefinedFilter<{\u -> u == admin}> CreditCard [Char] @-}
filterCreditCardHolder :: RefinedPersistFilter -> [Char] -> RefinedFilter CreditCard [Char]
filterCreditCardHolder f v = RefinedFilter CreditCardHolder v f

output :: Tagged a -> User -> ()
output = undefined

data CreditCard = CreditCard { creditCardNumber :: Int, creditCardHolder :: [Char]}
{-@
data CreditCard = CreditCard
	{ creditCardNumber :: Int
	, creditCardHolder :: [Char]
	}
@-}

{-@
data EntityField Creditcard typ <p :: User -> Bool> where 
   Field.CreditCardNumber :: EntityField <{\u -> u == admin}> CreditCard {v:_ | True}
 | Field.CreditCardHolder :: EntityField <{\u -> u == admin}> CreditCard {v:_ | True}
@-}

{-@ assume Prelude.error :: [Char] -> a @-} 
data EntityField a b where
  CreditCardNumber :: EntityField CreditCard Int
  CreditCardHolder :: EntityField CreditCard [Char]


{-@ selectTaggedData :: () -> Tagged<{\u -> u == admin}> [CreditCard] @-}
selectTaggedData :: () -> Tagged [CreditCard]
selectTaggedData () = selectCreditCard [filterCreditCardNumber EQUAL 3]

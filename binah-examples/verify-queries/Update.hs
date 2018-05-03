{-@ LIQUID "--no-adt" 	                           @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--ple" @-} 

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

class PersistEntity record where
    data EntityField record :: * -> *

instance PersistEntity Blob where
    {-@ data EntityField Blob typ where
        BlobXVal :: EntityField Blob {v:Int | v >= 0}
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ data Blob  = B { xVal :: {v:Int | v >= 0}, yVal :: Int } @-}
data Blob  = B { xVal :: Int, yVal :: Int }

{-@ data Update record typ = Update { updateField :: EntityField record typ, updateValue :: typ } @-}
data Update record typ = Update 
    { updateField :: EntityField record typ
    , updateValue :: typ
    } 

{-@ data variance Update covariant covariant contravariant @-}

{-@ createUpdate :: EntityField record a -> a -> Update record a @-}
createUpdate :: EntityField record a -> a -> Update record a
createUpdate field value = Update {
      updateField = field
    , updateValue = value
}

testUpdateQuery1 :: () -> Update Blob Int
testUpdateQuery1 () = createUpdate BlobXVal 3

testUpdateQuery2 :: () -> Update Blob Int
testUpdateQuery2 () = createUpdate BlobXVal 4

testUpdateQuery3 :: () -> Update Blob Int
testUpdateQuery3 () = createUpdate BlobXVal 5

testUpdateQuery4 :: () -> Update Blob Int
testUpdateQuery4 () = createUpdate BlobXVal 6

testUpdateQuery5 :: () -> Update Blob Int
testUpdateQuery5 () = createUpdate BlobXVal 7

testUpdateQuery6 :: () -> Update Blob Int
testUpdateQuery6 () = createUpdate BlobXVal 8

testUpdateQuery7 :: () -> Update Blob Int
testUpdateQuery7 () = createUpdate BlobXVal 9

testUpdateQuery8 :: () -> Update Blob Int
testUpdateQuery8 () = createUpdate BlobXVal 10

testUpdateQuery9 :: () -> Update Blob Int
testUpdateQuery9 () = createUpdate BlobXVal 11

testUpdateQuery10 :: () -> Update Blob Int
testUpdateQuery10 () = createUpdate BlobXVal 12

testUpdateQuery11 :: () -> Update Blob Int
testUpdateQuery11 () = createUpdate BlobXVal 13

testUpdateQuery12 :: () -> Update Blob Int
testUpdateQuery12 () = createUpdate BlobXVal 14

testUpdateQuery13 :: () -> Update Blob Int
testUpdateQuery13 () = createUpdate BlobXVal 15

testUpdateQuery14 :: () -> Update Blob Int
testUpdateQuery14 () = createUpdate BlobXVal 16

testUpdateQuery15 :: () -> Update Blob Int
testUpdateQuery15 () = createUpdate BlobXVal 17

testUpdateQuery16 :: () -> Update Blob Int
testUpdateQuery16 () = createUpdate BlobXVal 18

testUpdateQuery17 :: () -> Update Blob Int
testUpdateQuery17 () = createUpdate BlobXVal 19

testUpdateQuery18 :: () -> Update Blob Int
testUpdateQuery18 () = createUpdate BlobXVal 20

testUpdateQuery19 :: () -> Update Blob Int
testUpdateQuery19 () = createUpdate BlobXVal 21

testUpdateQuery20 :: () -> Update Blob Int
testUpdateQuery20 () = createUpdate BlobXVal 22


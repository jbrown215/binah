{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

class PersistEntity record where
    {-@ data EntityField @-}
    data EntityField record :: * -> *

{-@ data Blob  = B {} @-}
data Blob  = B {}

instance PersistEntity Blob where
    {-@ data EntityField record typ where
        BlobXVal :: EntityField Blob Int
      | BlobYVal :: EntityField Blob Int
    @-}
    data EntityField Blob typ where
        BlobXVal :: EntityField Blob Int
        BlobYVal :: EntityField Blob Int

{-@ reflect shouldntError @-}
shouldntError :: EntityField Blob a -> Bool
shouldntError BlobXVal = True
shouldntError BlobYVal = False

{-- We want to generate these refinements for the generated blob code --}
{-@ 
data Blob = Blob { blobXVal :: {x:Int | x >= 0}
                 , blobYVal :: {y:Int | y >= blobXVal}
                 }
@-}

{-@ data EntityField Blob typ where
    BlobXVal :: EntityField Blob {x:Int | x >= 0}
    BlobYVal :: EntityField b:Blob {y:Int | y >= (blobXVal b)}
@-}

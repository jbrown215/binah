{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module World where

{- Records are generated -}
{-@ data Blob = Blob {xVal :: {v:Int | v = 3}, yVal :: Int} @-}
data Blob = Blob {xVal :: Int, yVal :: Int}

{-@ data Range = Range {lower :: {v:Int | v = (xVal canonicalBlob)}, upper :: Int} @-}
data Range = Range {lower :: Int, upper :: Int}

{- Examples are generated -}
{-@ reflect canonicalBlob @-}
canonicalBlob = Blob 3 10

{-@ reflect canonicalRange @-}
canonicalRange = Range 3 14

{- World is represented as globally accessible, decentralized, canonical version
 - of the data in the database. This allows us to add refinements that reference
 - the refinements on other tables! -}
{- An alternative option is to acually make an explicit world instance with records 
 - whose values are those of the canonical representations:
 -}
data World = World {range :: Range, blob :: Blob}
world = World canonicalRange canonicalBlob

{-@ makeBlob :: () -> {b:Blob | xVal b == (xVal canonicalBlob)} @-}
makeBlob :: () -> Blob
makeBlob () = Blob {xVal = 3, yVal = 4}

makeRange :: () -> Range
makeRange () = Range {lower = 3, upper = 10}

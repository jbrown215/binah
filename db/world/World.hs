{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

{-# LANGUAGE ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module World where

data World

{-@ data Blob = Blob {xVal :: {v:Int | v == 3}, yVal :: Int} @-}
data Blob = Blob {xVal :: Int, yVal :: Int}


{-@ measure cannonicalBlob:: Blob @-}

{-@ data Range = Range {lower :: {v:Int | v == (xVal cannonicalBlob)}, upper :: Int} @-}
data Range = Range {lower :: Int, upper :: Int}

someRange :: () -> Range
someRange () = Range {lower = 3, upper = 4}

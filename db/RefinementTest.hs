{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--no-termination"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module RefinementTest where

{-@ data Blob = Blob { xVal :: Int, yVal :: {y:Int | y > xVal} } @-}
data Blob = Blob { xVal :: Int, yVal :: Int }

makeBlob = Blob {xVal = 3, yVal = 4}

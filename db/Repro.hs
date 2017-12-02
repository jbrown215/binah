{-@ LIQUID "--exact-data-con" @-}
{-# LANGUAGE EmptyDataDecls, ExistentialQuantification, KindSignatures, TypeFamilies, GADTs #-}

module Query where

import Prelude hiding (filter)

data User

{-@ data Tagged a <p :: User->Bool> = Tagged (content :: a) @-}
data Tagged a = Tagged a

{-@ data variance Tagged covariant contravariant @-}

instance Functor Tagged where
  fmap f (Tagged x) = Tagged (f x)

instance Applicative Tagged where
  pure  = Tagged
  -- f (a -> b) -> f a -> f b 
  (Tagged f) <*> (Tagged x) = Tagged (f x)

instance Monad Tagged where
  return x = Tagged x
  (Tagged x) >>= f = f x 
  (Tagged _) >>  t = t  
  fail          = error

{-@ instance Monad Tagged where 
     >>= :: forall <p :: User -> Bool, f:: a -> b -> Bool>. 
            x:Tagged <p> a
         -> (u:a -> Tagged <p> (b <f u>))
         -> Tagged <p> (b<f (content x)>); 
     >>  :: x:Tagged a
         -> Tagged b
         -> Tagged b;
     return :: forall <p :: User -> Bool>. a -> Tagged <p> a 
  @-}

{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RankNTypes #-}

module Demo where

import Prelude hiding (id)

-- exEasyGood =
--   let f = \x -> x + 1
--    in f 1

-- exEasyBad =
--   let f = \x -> x + 1
--    in f True

{-
f :: A
  A = B -> C
  x :: B
  B = Int
  C = Int

f :: B -> C
  B = Int

f :: Int -> Int
(f 1) :: Int

 -}


exTopLevel =
  let f = \x -> x -- f :: forall a . a -> a
   in let a = f 1 -- Int -> Int
       in f True  -- Bool -> Bool

{-
f :: A
  A = B -> C
  x :: B
  B = C

  B = Int
  B = True XXXXXXXXXX

f :: A
  A = B -> C
  x :: B
  B = C
f :: forall a . a -> a
  (f 1)
  f :: D -> D
  D = Int

  (f True)
  f :: E -> E
  E = Bool
 -}
 
data Both a b = Both a b

-- f :: forall a. (a -> a) -> Both Int Bool
f :: (forall a . a -> a) -> Both Int Bool
f = \x -> Both (x 1) (x True) 

{- 
f <== (forall a . a -> a) -> Both Int Bool
x :: forall a . a -> a

Both (x 1) (x True) <== Both Int Bool
  Both :: J -> K -> Both J K
  x :: A -> A
  A = Int
  J = Int

  x :: B -> B
  B = True
  K = Bool
-}

compose :: forall a b c . (b -> c) -> (a -> b) -> a -> c 
compose = \f -> \g -> \x -> f (g x)

id :: forall a . a -> a 
id = \x -> x

auto :: (forall a . a -> a) -> (forall a . a -> a)
auto = id id

exQL = compose auto auto
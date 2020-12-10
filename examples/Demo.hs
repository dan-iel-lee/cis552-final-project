module Demo where

exEasyGood =
  let f = \x -> x + 1
   in f 1

{-
1) let ....
f :: A
  A = B -> C
x :: B
  C = Int
  B = Int

2) f 1
  B = Int
 -}

exTopLevel =
  let f = \x -> x
   in let a = f 1
       in f True

{-
f :: A
  A = B -> C
  x :: B
  B = C

  B = Int
  B = True XXXXXXXXXX
 -}
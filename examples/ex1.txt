data Nat = Z | S Nat

pred :: Nat -> Nat 
pred = \n -> case n
  | Z -> Z
  | S m -> m ;

pred (S (S Z))
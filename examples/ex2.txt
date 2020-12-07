data List a = Nil | Cons a (List a)
data Maybe a = Nothing | Just a

head :: forall a . (List a) -> Maybe a
head = \l -> case l
  | Nil -> Nothing 
  | Cons x xs -> Just x ;

head (Cons 1 Nil)
data Both a b = Both a b

f :: (forall a . a -> a) -> Both Int Bool
f = \x -> Both (x 1) (x True) ;

let id = \x -> x
  in f id
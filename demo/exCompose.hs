compose :: forall a b c . (b -> c) -> (a -> b) -> a -> c 
compose = \f -> \g -> \x -> f (g x) ;

id :: forall a . a -> a 
id = \x -> x ;

auto :: (forall a . a -> a) -> (forall a . a -> a)
auto = id id ;

compose auto auto
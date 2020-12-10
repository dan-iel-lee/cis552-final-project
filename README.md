# project-cis552
# coming to a haskell near you...

## Demo ideas
- Propositions as types
- print constraints


## TODO type checking
- figure out polymorphic mgu
- ** Take context type variables into account
- allow recursion?
- figure out mguQL
- figure out scoping for type variables in constraints
- how does mgu work when you go under a forall binder?
  -  
- [x] combine InstMonad with TcMonad
- [x] Scoping in mgu using context
- [x] Constraints scoping
  - free unification variables
  - extra construct on Constraints
- [ ] get exList working
- [ ] type application
- [ ] make sure UVs are generalized at the end
- [ ] fix mgu under Foralls !!!!
  - Maybe by instantiating them and generating more constraints
- [ ] Check the `instantiateCase` is working correctly
- [ ] make sure order of `after` is correct in all places
- [ ] Look at paper for what strata are included in Constraints



- [ ] existentials?

## Properties for type checking
- unification variables never escape their bounds/scope

## Why abandon GADT solution?
I'm starting to realize that enforcing stratification at the implementation level is more of a headache
than a help. It requires a lot of type trickery, which can be fun, but also painful. What do we get
in return? Not much.

This is the initial README file for your project. You should update it as you
see fit.

## TODO

- Parsing
  - [x] update existing test cases with new syntax
  - [x] test cases for Datatype parsing and Declaration parsing
  - [x] parse types
  - [x] parse data constructors in expressions
  - [ ] ignore comments
- Type checking
  - [ ] write test cases with examples
- Evaluator
  - [ ] quickcheck property for running after N steps

## Building, running, and testing

This project compiles with `stack build`. You can add any needed dependencies
and update project metadata in [package.yaml](package.yaml).

You can run the main executable with `stack run`. The entry point for the
executable is in [Main.hs](app/Main.hs). It imports [Lib.hs](src/Lib.hs),
where the bulk of your code should be written.

Write your tests in [the test directory](test/Spec.hs). You can run the tests
with `stack test`.

Lastly, you can start a REPL with `stack ghci`.

## Components

- Parser
- Evaluator
- Typer

## Feature ideas

- pattern matching \*\*\*
- user defined types (inductive?) \*\*\*
- GADTs
- Type class constraints
- mutual recursion

Monad

- bind
- return

d = instance Monad (Maybe)

constraint dict:
Maybe => d

f Monad m => m a -> a

f (Just 1)

- Higher rank polymorphism
- type families
-

## Questions

- Do we need to do kind checking?

## Testing

## Order of stuff

- [ ] type annotations
- quickcheck Property: if valid ~ runs after n steps
-

### Checkpoint 2

- Parser
- Type annotations
- User defined types (non-recursive, \* kinded)
  - hopefully: also _ -> _ kinded

### Type classes

```haskell
data Weird = W (Weird -> Weird)
data Fix f = Fix (f (Fix f)) -- (* -> *) -> *



Weird -> Weird
(\ (W x) -> x (W x))

\x -> case x of
  (W a) -> a x

x : A
a : Weird -> Weird


inc :: Functor f => f Int -> F int
inc x = fmap (+ 1) x

inc :: forall f :: * -> * . Functor f -> f Int -> f int
inc dict x = dict.fmap (+ 1) x


type Functor f =
  { fmap :: forall a b . a -> b -> f a -> f b }

```

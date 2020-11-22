# project-cis552

This is the initial README file for your project. You should update it as you
see fit.

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

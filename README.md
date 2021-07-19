# glee

Glee (for *Glambda: Extended Edition*) is an experimental simply typed lambda calculus interpreter using type-level programming techniques. It is a fork/partial rewrite of Richard Eisenberg's [Glambda](#https://github.com/goldfirere/glambda).

The main modifications to Glambda are:

0) Switched Int to Peano Nats. (Doesn't really do anything ATM but make it slower, but will need for future experiments)

1) Added Record Types, Variant Types, a built-in List type, case expressions, and patterns to the language. (To do: Let expressions; Haskell report seems to indicate they can be piggyback'd off of case expressions)

2) Replaced some of the original singleton-esque GADT code w/ equivalent code that uses the Singletons library. (For improved ergonomics)

3) Addition of many type-classes, type families, helper GADTs, Data.Constraint Dict-building functions, etc. to facilitate type-safe Records and Variants.

4) Switched parser library to Megaparsec. 

5) Implemented user-defined types and named functions in the interpreter.

6) Small syntactical changes. Mainly `\x:Nat.x+x` -> `\x:Nat -> x+x` (Haskell style lambdas)

7) Removed Fix. (Wanted to experiment w/ a non-turing complete language; trivial to re-implement)

8) Generalized the ArithOps to a set of Op2 operators that don't just work on Ints/Nats. Implemented a few operators on lists/other types. 

9) Implemented a really stupid workaround for the inability to promoting Strings to Symbols. See the Ascii module.

10) Removed the step command. Something about the way I implemented operators broke it :_(


For right now, that's about it. You should be able to build with either `stack build` or `cabal new-build`. I kept getting permission errors w/ cabal and a haskeline dependency after changing linux distributions, but it worked alright before then so I'm guessing that's a me-thing. If you run the executable you get an interpreter that will evaluate STLC expressions. Due to the stupid workaround for string promotion, all function names, type names, record field names, and data constructor names have to contain only upper/lowercase letters or the interpreter will yell at you and crash. 

This is still highly experimental, there are a bunch of quirks/errors in the parser, don't rely on it for anything real etc. As of now the point is just to demonstrate a method for type-safe extensions to the STLC.


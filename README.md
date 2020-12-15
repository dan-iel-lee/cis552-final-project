# ghc 0.0.0.0.0.0.0.0.0.1alpha
**Tirtha Kharel, Karthik Macherla, Daniel Lee**

**PennKeys:** tkharel, kmacher, laniel

## Components
1. `Parser`: Generates an abstract syntax tree from a file using function `parseFile`
2. `TypeInf`: Main entry point is `top` which takes a file path and does all the type checking stuff.
              See comments in the file for details.
3. `Eval.hs` Takes a parsed `Expression` and using the `step` function, simplifies
              the expression until it can't be simplified anymore. Uses a substitution function `🔥`
              which substitutes variables as they are encountered in the future portions of expressions.



## External Libraries
The only external library we use is Hughes's `PrettyPrint`.
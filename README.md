# Quetzal

![a yellow dragon](quetzal.png "Quetzal")
<!-- 
Quetzal is syntactically imperative, semantically* dependently-typed.

\*well, not really. currently it "compiles\*\*" to Idris, which is dependently typed.

\*\*parses  -->

## Running 

In the toplevel directory, to setup the project, run `stack build`. To run the transformations on a file `files/a.qt` and output the generated code to a file `files/b.idr`, run 

`stack exec quetzal-exe -- "files/a.qt" "files/b.qt"`
You can also run `processFile "files/a.qt" "files/b.qt"` within a ghci shell. 

You can also test individual parsers `p` by running `parseFromFile p files/file.qt`.

## Syntax
The [syntax](syntax/grammar-fsm.txt) is presented in ebnf. Some [examples](syntax/examples.md). 

## Transformations 

### Imperative control flow 

### Iteration 

### Finite State Machines 

### Monadic do notation 
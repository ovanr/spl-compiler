# spl-compiler

## Installation

Make sure you have stack installed

1. `stack build`
2. `stack install alex`

## Running the lexer generator

1. `cd src/SPL/Compiler/Lexer`
2. `alex AlexLexGen.x -o AlexLexGen.hs `

You should now see the generated `AlexLex.hs` file.

## Running the tests

`stack test`

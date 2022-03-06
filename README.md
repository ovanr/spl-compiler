# spl-compiler

## Installation

Make sure you have stack installed and run:

1. `stack build`
2. `stack install alex`

## Running the lexer generator manually (done automatically with `stack build`)

1. `cd src/SPL/Compiler/Lexer`
2. `alex AlexLexGen.x`

You should now see the generated `AlexLex.hs` file.

## Running the compiler

Currently only Lexing and Parsing phases have been implemented
thus only the special flags `-l` (lexer dump) and `-p` (parser dump)
provide useful output

### Lexer dump

Return the result of the Lexer and exit
- `stack run -- spl-compiler -l --file SPL_FILE`

### Parser dump

Parse the source file and print the parsed result as actual code

- `stack run -- spl-compiler -p --file SPL_FILE`

## Running the tests

We have an extensive test suite which can be run using:
- `stack test`

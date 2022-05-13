# spl-compiler

## Installation

Make sure you have stack installed and run:

1. `stack install alex`
2. `stack build`

## Running the compiler

### Options
```
SPL-compiler

Usage: spl-compiler --file SRC [-l|--lexerDump] [-p|--parserDump]
                    [-t|--typeCheckerDump] [--noStaticEvaluation]
                    [-c|--coreDump] [--emitSSM] [--verbosity INT]
  Compiler for the SPL Language

Available options:
  --file SRC               Input file for compiling
  -l,--lexerDump           Only lex file and print the result
  -p,--parserDump          Only parse file and pretty print the result
  -t,--typeCheckerDump     Parse and typecheck, then pretty print the result
  --noStaticEvaluation     Do not staticly evaluate expressions and eliminate
                           dead code
  -c,--coreDump            Parse, typecheck, transform to CoreLang, then pretty
                           print result
  --emitSSM                Compile to SSM assembly
  --verbosity INT          The level of verbosity (default: 0)
  -h,--help                Show this help text
```

## Running the tests

We have an extensive test suite which can be run using:
- `stack test --coverage`

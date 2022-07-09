# spl-compiler

## Installation

Make sure you have stack installed and run:

1. `stack install alex`
2. `stack build`

## Running the compiler

### Options
```
SPL-compiler

Usage: spl-compiler FILENAME [-o|--output FILENAME] [-l|--lexerDump]
                    [-p|--parserDump] [-t|--typeCheckerDump] [--noOptimization]
  Compiler for the SPL Language

Available options:
  FILENAME                 Input file for compiling
  -o,--output FILENAME     Output file for writing result
  -l,--lexerDump           Only lex file and print the result
  -p,--parserDump          Only parse file and pretty print the result
  -t,--typeCheckerDump     Parse and typecheck, then pretty print the result
  --noOptimization         Do not perform constant folding and dead code elimination
  -h,--help                Show this help text
```

## Running the SSM assembly interpreter 

```bash
stack run spl-compiler -- -o out.ssm helloWorld.spl
./ssm.sh --cli --file out.ssm
```

## Running the tests

We have an extensive test suite which can be run using:
- `stack test --coverage`

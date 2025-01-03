# My Racket Compiler 🎾

This is my implementation of a racket subset compiler that was the semester long project of the Compilers course (CSCI-P 423) at Luddy. For those who are interested, the course GitHub can be found [here](https://github.com/IUCompilerCourse/Essentials-of-Compilation) where you can find the course webpage, textbook(s) and the student support code (which is what most of these files here are).

## What's here?

As stated above, a lot of the files here are just support code. These include:
- Intermediate language interpreters
    - `interp-*.rkt`
- Type checkers
    - `type-check-*.rkt`
- Runtime files (garbage collection and other small close coded stuff)
    - `runtime.c`
    - `runtime.o`
    - `runtime-config.rkt`
- General utility files
    - `Makefile`
    - `heap.rkt`
    - `multigraph.rkt`
    - `priority_queue.rkt`
    - `utilities.rkt`

The rest of the files are either test programs (with their corresponding inputs) or the compiler files. The most current iteration of my compiler can be found in the `compiler.rkt` file. As of now, this compiler includes all chapters up to and including `Dynamic Typing`. 

## The compilers! 

In the `compilers` folder, you can find the previous iterations of the compiler which each build upon the previous. The previous iterations are:
- `lvar.rkt`: Simple arithmetic and variable binding
- `lvar-ra.rkt`: Lvar now with register allocation
- `lif.rkt`: Conditionals and booleans
- `lwhile.rkt`: While loops and variable reassignment
- `lvec.rkt`: Vectors (tuples)
- `lvecof.rkt`: Arrays
- `lstruct.rkt`: Structs (which just translate to vectors)
- `lfun.rkt`: Functions
- `llambda.rkt`: Llambda functions
- `ldyn.rkt`: Dynamic typing

## How do I?

To actually run this compiler and generate an executable out of your racket file simply run

```shell
racket run-compiler.rkt my-file.rkt
```

The assembly ouput `my-file.s` and the exectuable `my-file.out` will be generated.

*my-file can be replaced by the name of any racket file you choose to compile
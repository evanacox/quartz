# Preface

These docs are split into several sections, many of which may be unwanted depending on what exactly you're looking for.

## Design & Overview



## QIR

The [QIR](./ir/index.md) section is dedicated to the Quartz IR and its design, including features, syntax, and other
general language things. This will rarely touch on exactly how those features are *implemented*. 

## Compiler APIs

Note that this book does not contain any information about the actual APIs of the compiler libraries, this book
is solely concerned with the overall design, architecture and implementation of the IR, optimizers and compiler.

The APIs can be found [here](https://pages.evanacox.io/quartz/api/quartz/).

## Compiler Internals

The [Compiler Internals](./compiler/index.md) chapter is solely dedicated to the specific implementation, architecture,
trickery and general features of the `kyanite` frontend. It will not explain the features of the language it references,
besides maybe referencing rules and explaining how those rules are implemented.

Knowledge of the entirety of [the language](./language/index.md) is assumed.

## Command-Line Tools


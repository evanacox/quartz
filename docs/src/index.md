# Preface

This book is split into several sections, many of which may be unwanted depending on what exactly you're looking for.

## Language

The [Language](./language/index.md) section is dedicated to the language itself, including features, syntax, and other
general language things. This will rarely touch on exactly how those features are *implemented*.

Note that this may be incomplete, if you find anything that's missing please create an issue (or a PR) to fix it!

## Compiler APIs

Note that this book does not contain any information about the actual APIs of the internal compiler libraries, this book
is solely concerned with the overall design, architecture and implementation of the language and the compiler itself.

The APIs can be found [here](https://pages.evanacox.io/kyanite/public/api/kyanite/index.html).

## Compiler Internals

The [Compiler Internals](./compiler/index.md) chapter is solely dedicated to the specific implementation, architecture,
trickery and general features of the `kyanite` frontend. It will not explain the features of the language it references,
besides maybe referencing rules and explaining how those rules are implemented.

Knowledge of the entirety of [the language](./language/index.md) is assumed.

## ABI

The [ABI](./abi/index.md) section is dedicated to the current ABI and environment of Kyanite that is
implemented/expected by the compiler.

This is stuff like the type layout, the Kyanite runtime library, etc.

Knowledge of the entirety of [the language](./language/index.md) is assumed.
# Sensitivity by Parametricity

## Artifact Overview

This repository contains the code for the paper titled "Sensitivity by
Parametricity", to appear on OOPSLA 2024. The paper explores the use of
parametricity to perform sensitivity analysis on user-defined functions,
additionally, it introduces a Haskell library called Spar that implements this
technique. Spar encodes value distances as type-level naturals, proving the
sensitivity of a function is reduced to type-checking!

**Authors:**
- Elisabet Lobo-Vesga (DPella AB)
- Carlos Tomé Cortiñas (Chalmers University)
- Alejandro Russo (Chalmers University)
- Marco Gaboardi (Boston University)

The artifact is structured as follows:

```
spar/
  ├── src/                  # Haskell source code of the library
        ├── Data.hs         # Useful data structures
        ├── Deep.hs         # Deep embedding of the Spar language
        ├── Example.hs      # Examples using Spar (inc. paper examples)
        ├── ManualProofs.hs # Proof's to aid the type-checker
        |── Run.hs          # Reflection and Reification of relational terms
        └── Spar.hs         # Library's API
  ├── cabal.project         # Cabal project file
  ├── Dockerfile            # Dockerfile for building the image
  |── LICENSE               # License file
  ├── README.md             # This file
  |── setup.sh              # Initialization script for the Docker container
  └── spar.cabal            # Cabal file for building the library
```

## System requirements

This artifact is distributed as a Docker image with the `spar` library built and
ready to use, as such, the only requirement is to have [Docker
Engine](https://docs.docker.com/engine/) installed in your system.

If you want to build the library from scratch, the minimal requirements are:

* [Glasgow Haskell Compiler (GHC)](https://www.haskell.org/ghc/) version 8.6.5
* [Cabal](https://www.haskell.org/cabal/) version 3.10.1.0
* [Z3 (the smt solver)](https://github.com/Z3Prover/z3) version >= 4.5

## Installation

This repo contains a [Dockerfile](./Dockerfile) to build a Docker image with the
`spar` library. Additionally, we provide a [setup script](./setup.sh) that
automates the process of building the image and running the container in
interactive mode.

After cloning the repository, you can build the Docker image by running the
following commands:

```bash
$ cd spar
$ ./setup.sh
```
The script opens a `bash` shell inside the container with the spar library
already built and ready to use.

## Usage

Once the Docker container is running, you can interact with the `spar` library
by running the Haskell interpreter.

```bash
$ cabal repl
```

In the Haskell prompt, you can explore the different functions
provided by the library. For example:

``` bash
*Spar> :t cswp
cswp :: Dist n (Int, Int) -> Dist n (Int, Int)
```

The examples can be loaded by importing the `Example` module:

```bash
*Spar> :module Examples
Prelude Examples> :t dpCDF
dpCDF
  :: (?d::Data.Proxy.Proxy d, GHC.TypeNats.KnownNat d,
      GHC.TypeNats.KnownNat eps) =>
     Data.Vec l m Bucket
     -> Data.Proxy.Proxy eps
     -> Deep.Dist 1 (Spar.SetOrigin Int)
     -> Deep.PM (m GHC.TypeNats.* eps) [(Bucket, Double)]

Prelude Examples> runCDF
[(0,15.088508887916229),(10,19.26063911103648),(20,24.403424680681656),(30,33.41216015467485),(40,33.37840042552355),(50,45.12906604164825),(60,62.31938886517386),(70,87.81957332084889)]
```

## Reproducing the results

The repository contains the code for the examples presented in the paper. You
can find them in the [Example.hs](./src/Example.hs) file. The type signatures of
these examples are annotated with the expected sensitivity and/or privacy level
as presented in the paper.

# Contact

If you have any questions or issues regarding the code, please contact Elisabet
Lobo-Vesga at <lobo@dpella.io>.

## License
Distribution of this artifact is subject to the terms of the MIT license. See
the [LICENSE](./LICENSE) file for details.

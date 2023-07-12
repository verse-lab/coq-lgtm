# Building Instructions

The version of Coq used in our development is **8.16.1**, where the version of underlying OCaml compiler is **4.12.0**. We list the required packages along with their respective versions (printed by `opam list`) as follows. 

```
coq-cfml               20220112
coq-cfml-basis         20220112
coq-cfml-stdlib        20220112
coq-fcsl-pcm           1.7.0
coq-mathcomp-algebra   1.15.0
coq-mathcomp-fingroup  1.15.0
coq-mathcomp-finmap    1.5.2
coq-mathcomp-ssreflect 1.15.0
coq-mathcomp-zify      1.3.0+1.12+8.13
coq-tlc                20211215
```

## Prerequisites

We recommend installing Coq and the required packages via OPAM. [The official page of OPAM](https://opam.ocaml.org/doc/Install.html) describes how to install and configure OPAM, and [the official page of Coq](https://coq.inria.fr/opam-using.html) describes how to install Coq and Coq packages with OPAM. 

## Build the Coq Project

Execute the following command in the terminal: 

```
make
```

Please note that warnings (in yellow colour) may appear during the compilation, but they will not cause the compilation to fail. 

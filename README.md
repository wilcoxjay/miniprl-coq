A Coq port of [MiniPRL](https://github.com/jozefg/miniprl). While we
make relatively heavy use of dependent types to keep track of bound
variables, there aren't really any proofs. A longer term goal is to
implement some the ideas of [Verified
NuPRL](http://www.nuprl.org/html/Nuprl2Coq/).


# Build instructions

## Overview

This project requires Coq 8.5pl1 (might work with other versions of
Coq 8.5, but certianly not with older versions). It furthermore
depends on the [StructTact](https://github.com/uwplse/StructTact)
library. Dependencies are detected by the `configure` script. If you
install `StructTact` as a sibling directory to this project, it will
be detected automatically. Otherwise you will need to edit
`StructTact_PATH` in `configure`.

## Example commands

Something like the following should work assuming a standard unix
system with Coq 8.5pl1 installed.

```
    # begin in the root directory of this repository

    # skip this part if you already have StructTact
    cd ..
    git clone git@github.com:uwplse/StructTact.git
    cd StructTact
    ./configure
    make

    cd ../miniprl-coq
    ./configure
    make
```

Verdi Serialized LockServ
=========================

An implementation of a lock server with serialization, verified in Coq using the Verdi framework and the Cheerios library.

Requirements
------------

Definitions and proofs:

- [`Coq 8.5`](https://coq.inria.fr/download)
- [`Verdi`](https://github.com/uwplse/verdi)
- [`StructTact`](https://github.com/uwplse/StructTact)
- [`Cheerios`](https://github.com/uwplse/cheerios)
- [`Verdi Cheerios`](https://github.com/DistributedComponents/verdi-cheerios)

Executable code:

- [`OCaml 4.02.3`](https://ocaml.org)
- [`OCamlbuild`](https://github.com/ocaml/ocamlbuild)
- [`ocamlfind`](http://projects.camlcity.org/projects/findlib.html)
- [`verdi-runtime`](https://github.com/DistributedComponents/verdi-runtime)

Building
--------

The recommended way to install the OCaml and Coq dependencies of Verdi LockServ is via [OPAM](https://coq.inria.fr/opam/www/using.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add distributedcomponents-dev http://opam-dev.distributedcomponents.net
opam install verdi StructTact verdi-runtime cheerios verdi-cheerios
```

Then, run `./configure` in the root directory.  This will check for the appropriate version of Coq and ensure all necessary dependencies can be located.

By default, the script assumes that `Verdi`, `StructTact`, `Cheerios`, and `Verdi Cheerios` are installed in Coq's `user-contrib` directory, but this can be overridden by setting the correct `_PATH` variables, e.g., `Verdi_PATH`.

Finally, run `make` in the root directory.

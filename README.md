A reflex based reimplementation of ghcide

TODO:

* Early cutoff (easy)
* Connect to a proper language server using reflex-process (easy)
* Work out whether using the shake interface for `define` is possible or desirable
  to support. It means the rules have to be slightly modified at the moment.
* Plumb diagnostics into the right place (easy)
* Garbage collection (harder)

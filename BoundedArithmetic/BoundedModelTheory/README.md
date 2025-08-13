This directory contains small modification to code copied straight from Lean4 mathlib (version from end of July 2025).

The modification is to not substitute `abbrev \exists \phi := \not \forall \not \phi`,
because it doesn't work well with our notion of Delta^1_1-formulas, Delta^B_0 formulas etc.

We add functionality to the namespace of this library (e.g. new notions of complexity
in the same namespace as ModelTheory.Complexity), but the code for them is in the main
directory of this library (i.e. in the parent of this folder) so that our contribution
is clearly displayed
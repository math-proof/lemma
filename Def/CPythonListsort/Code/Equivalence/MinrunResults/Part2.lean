/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

module

public import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
public import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
public import Mathlib
public import Theorem.CPythonListsort.Code.Equivalence.MinrunResults.Part2

@[expose] public section

/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

/-- Ceiling division used to state the balanced-sequence result without rationals. -/
def minrunCeilDiv (x modulus : Nat) : Nat :=
  (x + modulus - 1) / modulus

end CPythonListsort

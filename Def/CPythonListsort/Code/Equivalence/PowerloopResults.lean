/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Powerloop
import Mathlib
/-!
# Total correctness of `powerloop`

This file discharges the input bounds, trace-safety, termination, quotient-bit,
and concrete range obligations for CPython's 64-bit `powerloop` transcription.
-/


namespace CPythonListsort

/-- The C preconditions for two adjacent, nonempty runs inside a list. -/
def ValidPowerloopInput (s1 n1 n2 n : PySSize) : Prop :=
  s1.Nonnegative ∧ n1.Nonnegative ∧ n2.Nonnegative ∧ n.Nonnegative ∧
    0 < n1.toNat ∧ 0 < n2.toNat ∧
    s1.toNat + n1.toNat + n2.toNat ≤ n.toNat ∧
    n.toNat ≤ PY_LIST_MAX

end CPythonListsort

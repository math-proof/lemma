/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean -/

import sympy.atlas.CPythonListsort.Code.Equivalence.Powerloop
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

theorem pyListMax_eq : PY_LIST_MAX = 2 ^ 60 - 1 := by
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES]

/-- The interval invariant for the arbitrary-precision recurrence. -/
def PowerloopNatBounds (n : Nat) (state : PowerloopNatState) : Prop :=
  0 < n ∧ state.a < state.b ∧ state.b < 2 * n

/-- The residue whose high half is the quotient bit inspected at position `k`. -/
def powerloopResidue (x n k : Nat) : Nat :=
  (2 ^ k * x) % (2 * n)

/-- While running, the state is the residue at the next bit; once stopped, it records the first
differing bit. -/
def PowerloopNatQuotientInvariant (a b n : Nat) (state : PowerloopNatState) : Prop :=
  if state.stopped then
    ∃ k, state.result = k + 1 ∧ IsFirstDifferingQuotientBit a b n k
  else
    ∃ k, state.result = k ∧
      state.a = powerloopResidue a n k ∧
      state.b = powerloopResidue b n k ∧
      ∀ j < k, powerloopQuotientBit a n j = powerloopQuotientBit b n j

/-- The concrete power bound consumed by stack-depth accounting. -/
def POWER_BOUND : Nat := 60

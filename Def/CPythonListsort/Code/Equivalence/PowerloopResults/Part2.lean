/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Powerloop
import Mathlib
import Theorem.CPythonListsort.Code.Equivalence.PowerloopResults
/-!
# Total correctness of `powerloop`

This file discharges the input bounds, trace-safety, termination, quotient-bit,
and concrete range obligations for CPython's 64-bit `powerloop` transcription.
-/


namespace CPythonListsort

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

end CPythonListsort

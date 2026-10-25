/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean -/

import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib
import Structure.CPythonListsort.Code.Equivalence.Powerloop
/-!
# `powerloop` recurrence equivalence

This file projects the reviewed 64-bit transcription to a recurrence over
arbitrary-precision natural numbers.  The explicit safety trace records the
signed-comparison and shift-representability obligations inherited from C.
-/


namespace CPythonListsort

/-- Forget the 64-bit representation and retain the unsigned values. -/
def PowerloopState.toNatState (state : PowerloopState) : PowerloopNatState :=
  { result := state.result
    a := state.a.toNat
    b := state.b.toNat
    stopped := state.stopped }

/-- The quotient-bit recurrence from `listsort.txt`, over mathematical naturals. -/
def powerloopNatStep (n : Nat) (state : PowerloopNatState) : PowerloopNatState :=
  if state.stopped then
    state
  else
    let state := { state with result := state.result + 1 }
    let state :=
      if n ≤ state.a then
        { state with a := state.a - n, b := state.b - n }
      else if n ≤ state.b then
        { state with stopped := true }
      else
        state
    if state.stopped then
      state
    else
      { state with a := 2 * state.a, b := 2 * state.b }

/-- Iterate the arbitrary-precision recurrence with the same stopping convention. -/
def powerloopNatLoop : Nat → Nat → PowerloopNatState → PowerloopNatState
  | 0, _, state => state
  | fuel + 1, n, state =>
      if state.stopped then state else powerloopNatLoop fuel n (powerloopNatStep n state)

/-- Premises needed to project one finite-width loop step exactly. -/
def PowerloopStepSafe (n : PySSize) (state : PowerloopState) : Prop :=
  n.Nonnegative ∧
    state.a.Nonnegative ∧
    state.b.Nonnegative ∧
    state.a.toNat ≤ state.b.toNat ∧
    2 * state.a.toNat < 2 ^ 63 ∧
    2 * state.b.toNat < 2 ^ 63

/-- Safety evidence for every non-stopped state visited by a bounded loop. -/
def PowerloopTraceSafe : Nat → PySSize → PowerloopState → Prop
  | 0, _, _ => True
  | fuel + 1, n, state =>
      if state.stopped then True
      else PowerloopStepSafe n state ∧ PowerloopTraceSafe fuel n (powerloopStep n state)

/-- Natural-number specification initialized from the exact doubled midpoints. -/
def powerloopNatSpec (s1 n1 n2 n : PySSize) : PowerloopNatState :=
  let a := 2 * s1.toNat + n1.toNat
  let b := a + n1.toNat + n2.toNat
  powerloopNatLoop 64 n.toNat
    { result := 0, a := a, b := b, stopped := false }

/-- The zero-based quotient bit inspected by the natural-number recurrence. -/
def powerloopQuotientBit (a n k : Nat) : Nat :=
  ((2 ^ k * a) / n) % 2

/-- `k` is the first zero-based quotient-bit position at which `a / n` and `b / n` differ. -/
def IsFirstDifferingQuotientBit (a b n k : Nat) : Prop :=
  powerloopQuotientBit a n k = 0 ∧
    powerloopQuotientBit b n k = 1 ∧
    ∀ j < k, powerloopQuotientBit a n j = powerloopQuotientBit b n j

end CPythonListsort

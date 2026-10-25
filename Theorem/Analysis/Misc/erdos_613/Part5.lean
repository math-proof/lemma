import Mathlib
import Instance.Analysis.Misc.erdos_613.Part2
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

@[simp] lemma inBlock1_iff (v : V) : inBlock1 v ↔ (isA1 v ∨ isB1 v) := by
  cases v <;> simp [inBlock1, isA1, isB1]

@[simp] lemma inBlock2_iff (v : V) : inBlock2 v ↔ (isA2 v ∨ isB2 v) := by
  cases v <;> simp [inBlock2, isA2, isB2]

@[simp] lemma not_isA1_and_isB1 (v : V) : ¬ (isA1 v ∧ isB1 v) := by
  cases v <;> simp [isA1, isB1]

@[simp] lemma not_isA2_and_isB2 (v : V) : ¬ (isA2 v ∧ isB2 v) := by
  cases v <;> simp [isA2, isB2]

end PikhurkoN5

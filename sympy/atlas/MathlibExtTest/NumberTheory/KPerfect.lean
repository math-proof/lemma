/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/KPerfect.lean -/


import sympy.atlas.NumberTheory.KPerfect
import Lemma.Nat.KPerfect

example : Nat.IsKPerfect 2 6 := by
  rw [Nat.IsKPerfect]
  decide

example : Nat.IsKPerfect 3 120 := by
  rw [Nat.IsKPerfect]
  decide

example : ¬Nat.IsKPerfect 2 0 := by
  simp [Nat.IsKPerfect]

example : ¬Nat.IsKPerfect 0 6 := by
  rw [Nat.IsKPerfect]
  decide

example {k n : ℕ} (h : Nat.IsKPerfect k n) : 0 < k :=
  h.pos_k

example (n : ℕ) : Nat.IsKPerfect 2 n ↔ n.Perfect :=
  Nat.isKPerfect_two_iff n

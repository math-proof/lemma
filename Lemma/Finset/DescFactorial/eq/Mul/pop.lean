import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  (descPochhammer ℝ k).eval x = (x - (k - 1)) * (descPochhammer ℝ (k - 1)).eval x := by
-- proof
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simpa [Nat.add_sub_cancel, mul_comm] using descPochhammer_succ_eval n x


-- created on 2023-08-17
-- updated on 2023-08-26

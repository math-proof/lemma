import Mathlib.RingTheory.Polynomial.Pochhammer
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {k : ℕ}
-- given
  (hk : 0 < k) :
-- imply
  (descPochhammer ℝ k).eval x = x * (descPochhammer ℝ (k - 1)).eval (x - 1) := by
-- proof
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one]


-- created on 2023-08-17

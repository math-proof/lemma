import Mathlib.Analysis.SpecialFunctions.Log.Basic
import sympy.Basic


@[path]
private lemma main
  {n t : ℕ}
  {r β R p q : ℝ}
-- given
  (h₀ : t + 1 < n)
  (h₁ : r = -Real.log (p / q) * β + (if t = n - 1 then R else 0)) :
-- imply
  r = -Real.log (p / q) * β := by
-- proof
  have ht : t ≠ n - 1 := by
    omega
  rw [h₁]
  simp [ht]


-- created on 2026-10-11
-- updated on 2026-10-17

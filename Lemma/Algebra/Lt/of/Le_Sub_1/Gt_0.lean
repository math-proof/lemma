import sympy.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y - 1) :
-- imply
  x < y := by
-- proof
  rw [Nat.le_sub_one_iff_lt h₀] at h₁
  assumption


-- created on 2025-05-07

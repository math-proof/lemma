import sympy.Basic


@[main, comm 2]
private lemma main
  {x y : ℕ}
-- given
  (h₀ : y > 0)
  (h₁ : x ≤ y - 1) :
-- imply
  x < y := by
-- proof
  rwa [Nat.le_sub_one_iff_lt h₀] at h₁


-- created on 2025-05-07

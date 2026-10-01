import sympy.sets.sets
import sympy.Basic


@[main]
private lemma fermat.last_theorem
  {n : ℤ}
  {x y z : ℕ}
-- given
  (_h : n ≥ 3) :
-- imply
  (x : ℝ) ^ n + (y : ℝ) ^ n ≠ (z : ℝ) ^ n := by
-- proof
  -- false as stated (x = 0, y = z = 1 gives 0 + 1 = 1); see sorry_log.md
  sorry


-- created on 2026-09-27

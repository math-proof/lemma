import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≠ y)
  (k : ℤ) :
-- imply
  (if x = k then (1 : ℝ) else 0) * (if y = k then 1 else 0) = 0 := by
-- proof
  by_cases h₁ : x = k
  · rw [if_pos h₁, if_neg (fun h₂ => h (h₁.trans h₂.symm)), mul_zero]
  · rw [if_neg h₁, zero_mul]


-- created on 2020-02-06

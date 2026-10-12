import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≠ y)
  (k : ℤ) :
-- imply
  (if x = k then (1 : ℝ) else 0) * (if y = k then 1 else 0) = 0 := by
-- proof
  if h₁ : x = k then
    rw [ite_eq_left h₁, ite_eq_right (fun h₂ => h (h₁.trans h₂.symm)), mul_zero]
  else
    rw [ite_eq_right h₁, zero_mul]


-- created on 2020-02-06

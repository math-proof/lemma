import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < b)
  (h₁ : x ∈ Set.Ioi 0) :
-- imply
  a * x < b * x := by
-- proof
  exact mul_lt_mul_of_pos_right h₀ (Set.mem_Ioi.mp h₁)


-- created on 2021-10-02

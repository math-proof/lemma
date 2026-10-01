import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b d : ℝ}
-- given
  (hd : d > 0)
  (h : x * d ∈ Set.Icc (a * d) (b * d)) :
-- imply
  x ∈ Set.Icc a b := by
-- proof
  exact ⟨le_of_mul_le_mul_right h.1 hd, le_of_mul_le_mul_right h.2 hd⟩


-- created on 2019-06-25

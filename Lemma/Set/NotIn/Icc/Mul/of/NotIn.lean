import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b d : ℝ}
-- given
  (h : x ∉ Set.Ico a b)
  (hd : d > 0) :
-- imply
  x * d ∉ Set.Ico (a * d) (b * d) := by
-- proof
  intro hmem
  exact h ⟨(mul_le_mul_iff_left₀ hd).mp hmem.1, (mul_lt_mul_iff_left₀ hd).mp hmem.2⟩


-- created on 2021-06-07

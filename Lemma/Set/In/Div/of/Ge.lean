import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n b : ℝ}
-- given
  (h : n ≥ b)
  (hb : 0 < b) :
-- imply
  1 / n ∈ Set.Ioc 0 (1 / b) := by
-- proof
  have hn : 0 < n := lt_of_lt_of_le hb h
  exact ⟨one_div_pos.mpr hn, one_div_le_one_div_of_le hb h⟩


-- created on 2023-10-04

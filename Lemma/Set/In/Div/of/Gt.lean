import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℝ}
-- given
  (h : n > b)
  (hb : 0 < b) :
-- imply
  1 / n ∈ Set.Ioo 0 (1 / b) := by
-- proof
  have hn : 0 < n := hb.trans h
  exact ⟨one_div_pos.mpr hn, one_div_lt_one_div_of_lt hb h⟩


-- created on 2023-10-04

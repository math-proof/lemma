import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ioi 0 ∪ Set.Iio 0) :
-- imply
  1 / x ∈ Set.Ioi 0 ∪ Set.Iio 0 := by
-- proof
  rcases h with h | h
  · exact Or.inl (Set.mem_Ioi.mpr (one_div_pos.mpr (Set.mem_Ioi.mp h)))
  · exact Or.inr (Set.mem_Iio.mpr (one_div_neg.mpr (Set.mem_Iio.mp h)))


-- created on 2026-09-27

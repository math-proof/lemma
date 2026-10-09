import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Iio 0) :
-- imply
  |x| ∈ Set.Ioi 0 := by
-- proof
  exact Set.mem_Ioi.mpr (abs_pos.mpr (ne_of_lt (Set.mem_Iio.mp h)))


-- created on 2020-04-15

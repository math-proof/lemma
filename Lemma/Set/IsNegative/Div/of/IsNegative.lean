import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Iio 0) :
-- imply
  1 / x ∈ Set.Iio 0 := by
-- proof
  exact Set.mem_Iio.mpr (one_div_neg.mpr (Set.mem_Iio.mp h))


-- created on 2020-04-13

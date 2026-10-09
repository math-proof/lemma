import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n b : ℝ}
-- given
  (h : n ∈ Set.Iio b) :
-- imply
  n < b := by
-- proof
  exact Set.mem_Iio.mp h


-- created on 2020-04-09

import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n b : ℤ}
-- given
  (h : n < b) :
-- imply
  n ∈ Set.Iio b := by
-- proof
  exact Set.mem_Iio.mpr h


-- created on 2021-08-05

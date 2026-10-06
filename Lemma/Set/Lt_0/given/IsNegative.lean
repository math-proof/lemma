import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x < 0) :
-- imply
  x ∈ Set.Iio 0 :=
-- proof
  Set.mem_Iio.mpr h


-- created on 2020-04-25

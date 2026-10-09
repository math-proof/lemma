import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℤ}
-- given
  (h : n ≤ b) :
-- imply
  n ∈ Iio (b + 1) :=
-- proof
  Int.lt_add_one_iff.mpr h


-- created on 2021-05-18

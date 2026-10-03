import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {b n : α}
-- given
  (h : n ∈ Iio b) :
-- imply
  n < b :=
-- proof
  Set.mem_Iio.mp h


-- created on 2020-04-09

import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n b : ℤ}
-- given
  (h₀ : n < b) :
-- imply
  n ∈ Set.Iio b :=
-- proof
  Set.mem_Iio.mpr h₀


-- created on 2018-02-28
-- updated on 2026-10-17

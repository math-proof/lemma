import sympy.Basic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n.fmod d < d := by
-- proof
  -- Use the property of the floored modulus to show that the remainder is less than the divisor.
  apply Int.fmod_lt_of_pos (H := h)


-- created on 2025-03-28

import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x d : ℤ}
-- given
  (h : x = 0) :
-- imply
  x % d = 0 := by
-- proof
  rw [h]
  exact Int.zero_emod d


-- created on 2021-07-28

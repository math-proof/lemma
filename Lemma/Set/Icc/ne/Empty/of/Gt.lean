import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : a < b) :
-- imply
  Set.Ioo a b ≠ ∅ := by
-- proof
  exact (Set.nonempty_Ioo.mpr h).ne_empty


-- created on 2021-04-17

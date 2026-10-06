import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℤ}
-- given
  (h : a < b) :
-- imply
  Finset.Ico a b ≠ ∅ := by
-- proof
  exact (Finset.nonempty_Ico.mpr h).ne_empty


-- created on 2021-04-18

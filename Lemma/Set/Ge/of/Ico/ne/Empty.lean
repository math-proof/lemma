import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h : Finset.Ico a b ≠ ∅) :
-- imply
  a ≤ b := by
-- proof
  have hne : (Finset.Ico a b).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
  exact (Finset.nonempty_Ico.mp hne).le


-- created on 2021-06-21

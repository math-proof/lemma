import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℤ}
-- given
  (h : Finset.Ico a b ≠ ∅) :
-- imply
  a - b < 0 := by
-- proof
  have hlt : a < b := Finset.nonempty_Ico.mp (Finset.nonempty_iff_ne_empty.mpr h)
  omega


-- created on 2021-06-21

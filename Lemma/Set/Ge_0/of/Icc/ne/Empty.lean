import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Icc a b ≠ ∅) :
-- imply
  0 ≤ b - a := by
-- proof
  have hle : a ≤ b := Set.nonempty_Icc.mp (Set.nonempty_iff_ne_empty.mpr h)
  linarith


-- created on 2019-09-23

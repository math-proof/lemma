import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Icc a b ≠ ∅) :
-- imply
  a ≤ b := by
-- proof
  exact Set.nonempty_Icc.mp (Set.nonempty_iff_ne_empty.mpr h)


-- created on 2021-05-07

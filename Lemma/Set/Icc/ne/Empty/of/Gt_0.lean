import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b ≠ ∅) :
-- imply
  0 < b - a := by
-- proof
  have hlt : a < b := Set.nonempty_Ioc.mp (Set.nonempty_iff_ne_empty.mpr h)
  linarith


-- created on 2021-05-09

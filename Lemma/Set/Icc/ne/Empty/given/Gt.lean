import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b ≠ ∅) :
-- imply
  a < b := by
-- proof
  exact Set.nonempty_Ioc.mp (Set.nonempty_iff_ne_empty.mpr h)


-- created on 2021-05-08

import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b ≠ ∅) :
-- imply
  a - b < 0 := by
-- proof
  apply sub_neg.mpr (Set.nonempty_Ioc.mp (Set.nonempty_iff_ne_empty.mpr h))


-- created on 2021-05-12

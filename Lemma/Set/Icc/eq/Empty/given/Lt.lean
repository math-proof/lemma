import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Icc a b = ∅) :
-- imply
  b < a := by
-- proof
  by_contra hle
  push_neg at hle
  exact (Set.nonempty_Icc.mpr hle).ne_empty h


-- created on 2021-05-02

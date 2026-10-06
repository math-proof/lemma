import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Icc a b = ∅) :
-- imply
  b - a < 0 := by
-- proof
  have hlt : b < a := by
    by_contra hle
    push_neg at hle
    exact (Set.nonempty_Icc.mpr hle).ne_empty h
  linarith


-- created on 2021-05-03

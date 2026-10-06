import Lemma.Set.Gt.of.Icc.eq.Empty
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Icc a b = ∅) :
-- imply
  b - a < 0 :=
-- proof
  sub_neg.mpr (Set.Gt.of.Icc.eq.Empty h)


-- created on 2021-05-07

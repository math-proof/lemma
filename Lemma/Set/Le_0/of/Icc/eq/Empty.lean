import Lemma.Set.Le.of.Icc.eq.Empty
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b = ∅) :
-- imply
  b - a ≤ 0 :=
-- proof
  sub_nonpos.mpr (Set.Le.of.Icc.eq.Empty h)


-- created on 2021-05-06

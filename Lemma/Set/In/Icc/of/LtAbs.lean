import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| < a) :
-- imply
  x ∈ Ioo (-a) a := by
-- proof
  exact Set.mem_Ioo.mpr (abs_lt.mp h)


-- created on 2021-01-07

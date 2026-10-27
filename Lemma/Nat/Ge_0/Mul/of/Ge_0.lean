import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ≥ 0)
  (ha : a ≥ 0) :
-- imply
  x * a ≥ 0 := by
-- proof
  exact mul_nonneg h ha


-- created on 2019-06-15

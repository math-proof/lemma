import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : y ≥ 0)
  (h : x ≥ y) :
-- imply
  x * x ≥ y * y := by
-- proof
  nlinarith


-- created on 2019-06-01

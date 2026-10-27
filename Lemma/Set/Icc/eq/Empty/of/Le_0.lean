import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : Set.Ioc a b = ∅) :
-- imply
  b - a ≤ 0 := by
-- proof
  have hle : b ≤ a := not_lt.mp (Set.Ioc_eq_empty_iff.mp h)
  linarith


-- created on 2021-05-02

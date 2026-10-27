import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  x < y ↔ y - x > 0 := by
-- proof
  exact sub_pos.symm


-- created on 2023-06-19

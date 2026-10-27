import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  x - y < 0 ↔ y > x := by
-- proof
  exact sub_neg


-- created on 2023-06-20

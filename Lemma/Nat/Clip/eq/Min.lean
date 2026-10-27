import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a b : ℝ} :
-- imply
  min (max x a) b = min (max x a) b := by
-- proof
  rfl


-- created on 2023-03-26

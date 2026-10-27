import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma reverse
  {x a : ℝ} :
-- imply
  x ≤ a ↔ a ≥ x := by
-- proof
  exact Iff.rfl


-- created on 2019-11-26

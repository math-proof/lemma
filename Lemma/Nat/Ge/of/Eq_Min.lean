import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b M : ℝ}
-- given
  (h : min a b = M) :
-- imply
  a ≥ M := by
-- proof
  exact h ▸ min_le_left a b


-- created on 2023-04-23

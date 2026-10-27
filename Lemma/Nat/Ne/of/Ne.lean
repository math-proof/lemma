import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma reverse.given
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


@[path]
private lemma reverse
  {a b : α}
-- given
  (h : a ≠ b) :
-- imply
  b ≠ a := by
-- proof
  exact h.symm


-- created on 2020-02-05

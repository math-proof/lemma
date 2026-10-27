import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a b c : α}
-- given
  (h : x = a ∨ x = b ∨ x = c) :
-- imply
  x ∈ ({a, b, c} : Set α) := by
-- proof
  obtain rfl | rfl | rfl := h <;> simp


-- created on 2018-11-19

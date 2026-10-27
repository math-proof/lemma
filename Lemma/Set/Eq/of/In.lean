import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a : α}
-- given
  (h : x = a) :
-- imply
  x ∈ ({a} : Set α) := by
-- proof
  rw [h, Set.mem_singleton_iff]


-- created on 2020-04-17

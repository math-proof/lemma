import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (i : Fin n) :
-- imply
  (i : ℕ) ∈ range n \ range i := by
-- proof
  simp_all


-- created on 2025-05-18

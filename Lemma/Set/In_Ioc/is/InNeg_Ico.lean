import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x a b : α) :
-- imply
  x ∈ Ioc a b ↔ -x ∈ Ico (-b) (-a) := by
-- proof
  aesop


-- created on 2025-09-30

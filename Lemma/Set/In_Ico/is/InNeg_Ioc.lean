import sympy.sets.sets
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x a b : α) :
-- imply
  x ∈ Ico a b ↔ -x ∈ Ioc (-b) (-a) := by
-- proof
  aesop


-- created on 2025-09-30

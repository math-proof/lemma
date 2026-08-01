import sympy.sets.sets
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x a b : α) :
-- imply
  x ∈ Icc a b ↔ -x ∈ Icc (-b) (-a) := by
-- proof
  aesop


-- created on 2018-10-06

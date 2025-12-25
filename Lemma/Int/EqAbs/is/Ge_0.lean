import Lemma.Int.Abs.eq.IteGe_0
open Int


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
-- given
  (x : α) :
-- imply
  |x| = x ↔ x ≥ 0 :=
-- proof
  abs_eq_self


-- created on 2025-10-01

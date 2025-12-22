import Lemma.Int.LtSubS.is.Lt
import Lemma.Nat.LtAddS.is.Lt
open Int Nat


@[main, comm, mp, mpr]
private lemma main
  [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
-- given
  (x y : α) :
-- imply
  x < y ↔ x - y < 0 := by
-- proof
  constructor <;> 
    intro h
  ·
    have := LtAddS.of.Lt y h
    simp_all
  ·
    have h := LtSubS.of.Lt (-y) h
    simp at h
    assumption


-- created on 2025-03-24
-- updated on 2025-12-22

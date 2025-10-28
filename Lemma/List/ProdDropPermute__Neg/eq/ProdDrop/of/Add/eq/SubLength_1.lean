import Lemma.List.DropPermute__Neg.eq.Cons_TakeDrop.of.Add.eq.SubLength_1
import Lemma.List.EqAppendTake__ListGet.of.EqLength_Add_1
import Lemma.Nat.Mul
open List Nat


@[main, comm]
private lemma main
  [CommMonoid α]
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  ((s.permute ⟨i + d, by grind⟩ (-d)).drop i).prod = (s.drop i).prod := by
-- proof
  rw [← EqAppendTake__ListGet.of.EqLength_Add_1 (s := s.drop i) (n := d) (by simp; omega)]
  rw [DropPermute__Neg.eq.Cons_TakeDrop.of.Add.eq.SubLength_1 h]
  simp
  rw [Mul.comm]


-- created on 2025-10-28

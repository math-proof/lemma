import Lemma.List.DropSet.eq.SetDrop.of.Ge
import Lemma.List.GetDrop.eq.Get_Add.of.GtLength_Add
import Lemma.List.ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  [CommMonoid α]
  {s : List α}
-- given
  (h : i < s.length)
  (h : i ≥ j)
  (n : α) :
-- imply
  ((s.set i (n * s[i])).drop j).prod = n * (s.drop j).prod := by
-- proof
  rw [DropSet.eq.SetDrop.of.Ge (by grind)]
  have := ProdSet__Mul_Get.eq.Mul_Prod.of.Lt_Length (s := s.drop j) (i := i - j) (by grind) n
  rw [GetDrop.eq.Get_Add.of.GtLength_Add (by grind)] at this
  simp [EqAdd_Sub.of.Ge h] at this
  assumption


-- created on 2025-11-22

import Lemma.List.DropDrop.eq.Drop_Add
import Lemma.List.DropSet.eq.SetDrop.of.Ge
import Lemma.List.ProdSet.eq.MulProd_Mul_Prod.of.GtLength
import Lemma.List.TakeDrop.eq.DropTake
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.Nat.MulMul.eq.Mul_Mul
open List Nat


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_len : s.length > i)
  (h_ge : i ≥ j)
  (n : α) :
-- imply
  ((s.set i n).drop j).prod = ((s.take i).drop j).prod * n * (s.drop (i + 1)).prod := by
-- proof
  rw [DropSet.eq.SetDrop.of.Ge h_ge]
  rw [ProdSet.eq.MulProd_Mul_Prod.of.GtLength (by grind)]
  rw [DropDrop.eq.Drop_Add]
  rw [TakeDrop.eq.DropTake]
  rw [Add_Add.eq.AddAdd]
  rw [EqAdd_Sub.of.Ge h_ge]
  rw [MulMul.eq.Mul_Mul]


-- created on 2026-08-01

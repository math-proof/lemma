import Lemma.List.TakeDrop.eq.DropTake
import Lemma.List.DropTake.eq.TakeDrop
import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.Nat.Add
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  (s.drop i).take (d + 1) = s[i] :: (s.drop (i + 1)).take d := by
-- proof
  rw [TakeDrop.eq.DropTake]
  conv_rhs =>
    rw [TakeDrop.eq.DropTake]
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength]
  ·
    apply congrArg₂
    ·
      rw [GetTake.eq.Get.of.Lt_LengthTake]
    ·
      rw [Add.comm (a := d)]
      rw [Add_Add.eq.AddAdd]
  ·
    simpa


-- created on 2025-10-24

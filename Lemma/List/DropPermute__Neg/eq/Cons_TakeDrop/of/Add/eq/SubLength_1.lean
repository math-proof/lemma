import Lemma.List.Drop.eq.Cons_Drop_Add_1
import Lemma.List.DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1
import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
import Lemma.List.TakeDrop.eq.DropTake
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute ⟨i + d, by grind⟩ (-d)).drop i = s[i + d] :: (s.drop i).take d := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1 (v := s.permute ⟨i + d, by grind⟩ (-d)) (i := ⟨i, by simp⟩)]
  simp [DropPermute__Neg.eq.TakeDrop.of.Add.eq.SubLength_1 h]
  rw [GetPermute__Neg.eq.Get_Add.of.GtLength_Add]



-- created on 2025-10-28

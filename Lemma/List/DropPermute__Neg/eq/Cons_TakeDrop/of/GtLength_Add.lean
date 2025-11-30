import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.List.DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add
import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute ⟨i + d, by grind⟩ (-d)).drop i = s[i + d] :: (s.drop i).take d ++ s.drop (i + d + 1) := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by simp; omega) (s := s.permute ⟨i + d, by grind⟩ (-d)) (i := i)]
  simp [GetPermute__Neg.eq.Get_Add.of.GtLength_Add h]
  rw [DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add h]


-- created on 2025-10-29
-- updated on 2025-11-30

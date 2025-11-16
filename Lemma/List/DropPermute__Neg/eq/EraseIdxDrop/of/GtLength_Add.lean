import Lemma.List.DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
import Lemma.Nat.AddAdd.eq.Add_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute ⟨i + d, by grind⟩ (-d)).drop (i + 1) = (s.drop i).eraseIdx d := by
-- proof
  rw [DropPermute__Neg.eq.AppendTakeDrop.of.GtLength_Add h]
  simp [EraseIdx.eq.Append_Drop_Add_1]
  rw [AddAdd.eq.Add_Add]


-- created on 2025-11-15

import Lemma.List.Drop.eq.Nil.of.Ge_Length
import Lemma.List.DropAppend.eq.AppendDrop.of.GeLength
import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
open List


@[main]
private lemma main
-- given
  (h : i > j)
  (s : List α) :
-- imply
  (s.eraseIdx i).drop j = (s.take i).drop j ++ s.drop (i + 1) := by
-- proof
  if h_j : j ≥ s.length then
    repeat rw [Drop.eq.Nil.of.Ge_Length (by grind)]
    simp
  else
    rw [EraseIdx.eq.Append_Drop_Add_1]
    rw [DropAppend.eq.AppendDrop.of.GeLength]
    simp
    omega


-- created on 2025-11-21

import Lemma.List.DropAppend.eq.AppendDrop.of.GeLength
import Lemma.List.InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_i : s.length ≥ j)
  (h_j : i ≥ j)
  (x : α) :
-- imply
  (s.insertIdx i x).drop j = (s.drop j).insertIdx (i - j) x := by
-- proof
  rw [InsertIdx.eq.Append_InsertIdxDrop.of.Ge.GeLength (by omega) h_j]
  rw [DropAppend.eq.AppendDrop.of.GeLength]
  ·
    simp
  ·
    simp
    omega


-- created on 2025-11-26

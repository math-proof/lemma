import Lemma.List.InsertIdx.eq.Append_Cons.of.GeLength
import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.List.SetCons.eq.Cons_Set
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h_i : i < s.length)
  (n : α)
  (a : α) :
-- imply
  (s.insertIdx i a).set i.succ n = (s.set i n).insertIdx i a := by
-- proof
  induction s generalizing i with
  | nil =>
    exact Fin.elim0 ⟨i, by grind⟩
  | cons x xs ih =>
    match i with
    | 0 =>
      rw [InsertIdx.eq.Append_Cons.of.GeLength (by simp)]
      rw [Set.eq.AppendTake__Cons_Drop.of.GtLength (by simp)]
      rw [InsertIdx.eq.Append_Cons.of.GeLength (by simp)]
      simp
    | i + 1 =>
      rw [InsertIdxCons.eq.Cons_InsertIdx]
      repeat rw [SetCons.eq.Cons_Set]
      rw [ih (by grind)]
      rw [InsertIdxCons.eq.Cons_InsertIdx]


-- created on 2026-07-12

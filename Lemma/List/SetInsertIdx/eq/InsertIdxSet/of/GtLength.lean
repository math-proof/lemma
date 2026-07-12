import Lemma.List.InsertIdx.eq.Append_Cons.of.GeLength
import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx
import Lemma.List.Set.eq.AppendTake__Cons_Drop.of.GtLength
import Lemma.List.SetCons.eq.Cons_Set
open List


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_i : i < s.length)
  (n : ℕ) :
-- imply
  (s.insertIdx i 1).set (i + 1) n = (s.set i n).insertIdx i 1 := by
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

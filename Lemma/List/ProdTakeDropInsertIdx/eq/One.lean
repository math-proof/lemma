import Lemma.List.DropInsertIdx.eq.InsertIdxDrop.of.Ge.GeLength
open List


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (((s.insertIdx i 1).drop i).take 1).prod = 1 := by
-- proof
  if h_i : i ≤ s.length then
    rw [DropInsertIdx.eq.InsertIdxDrop.of.Ge.GeLength (by grind) (by grind)]
    simp
  else
    have h_i : i > s.length := by grind
    rw [Drop.eq.Nil.of.LeLength (by grind)]
    simp


-- created on 2026-07-22

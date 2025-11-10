import Lemma.List.EraseIdx.eq.Append_Drop_Add_1
open List


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  (s.eraseIdx i).prod = (s.take i).prod * (s.drop (i + 1)).prod := by
-- proof
  simp [EraseIdx.eq.Append_Drop_Add_1]


-- created on 2025-11-09

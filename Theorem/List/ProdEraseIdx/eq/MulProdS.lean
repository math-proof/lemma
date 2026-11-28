module

public import Initialize.Tactic.Attr.Basic

public import Theorem.List.EraseIdx.eq.Append_Drop_Add_1

public section

open List


@[path, comm]
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

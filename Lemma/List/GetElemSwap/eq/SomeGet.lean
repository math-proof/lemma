import Batteries.Data.List.Lemmas
import Lemma.List.Swap
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i j : Fin s.length) :
-- imply
  (s.swap i j)[i]? = some s[j] := by
-- proof
  rw [Fin.getElem?_fin]
  rw [getElem?_eq_getElem]
  rw [List.getElem_swap_left_of_lt j.isLt]
  rw [Fin.getElem_fin]
  simp


@[main]
private lemma left
-- given
  (s : List α)
  (i j : Fin s.length) :
-- imply
  (s.swap i j)[j]? = some s[i] := by
-- proof
  rw [Swap]
  rw [main]


-- created on 2025-05-15
-- updated on 2026-08-24

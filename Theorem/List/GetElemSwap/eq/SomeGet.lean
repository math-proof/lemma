module

public import Mathlib

public import Batteries.Data.List.Lemmas
public import Theorem.List.Swap

public section

open List


public theorem List.GetElemSwap.eq.SomeGet
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


public theorem List.GetElemSwap.eq.SomeGet.left
-- given
  (s : List α)
  (i j : Fin s.length) :
-- imply
  (s.swap i j)[j]? = some s[i] := by
-- proof
  rw [Swap]
  exact GetElemSwap.eq.SomeGet s j i


-- created on 2025-05-15
-- updated on 2026-08-24

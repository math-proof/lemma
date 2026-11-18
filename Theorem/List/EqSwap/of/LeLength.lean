module

public import Mathlib

public import Batteries.Data.List.Lemmas

public section


public theorem List.EqSwap.of.LeLength.left
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length ≤ i)
  (j : ℕ) :
-- imply
  s.swap i j = s :=
-- proof
  List.swap_eq_of_ge_left h


public theorem List.EqSwap.of.LeLength
  {s : List α}
-- given
  (h : s.length ≤ j)
  (i : ℕ) :
-- imply
  s.swap i j = s :=
-- proof
  List.swap_eq_of_ge_right h


-- created on 2025-06-07
-- updated on 2026-10-26

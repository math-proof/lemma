import Batteries.Data.List.Lemmas
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  s.swap i j = s.swap j i :=
-- proof
  List.swap_comm


-- created on 2025-05-16
-- updated on 2026-08-24

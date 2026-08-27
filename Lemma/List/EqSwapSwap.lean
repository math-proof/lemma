import Batteries.Data.List.Lemmas
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.swap i j).swap j i = s :=
-- proof
  List.swap_swap_flip


@[main]
private lemma swap
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.swap i j).swap i j = s :=
-- proof
  List.swap_swap


-- created on 2025-05-17
-- updated on 2026-08-24

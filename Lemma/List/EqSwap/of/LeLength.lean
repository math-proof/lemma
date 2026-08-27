import Batteries.Data.List.Lemmas
import sympy.Basic


@[main]
private lemma left
  {s : List α}
  {i : ℕ}
-- given
  (h : s.length ≤ i)
  (j : ℕ) :
-- imply
  s.swap i j = s :=
-- proof
  List.swap_eq_of_ge_left h


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ j)
  (i : ℕ) :
-- imply
  s.swap i j = s :=
-- proof
  List.swap_eq_of_ge_right h


-- created on 2025-06-07
-- updated on 2026-08-24

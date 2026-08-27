import Batteries.Data.List.Lemmas
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i j : ℕ) :
-- imply
  (s.swap i j).length = s.length :=
-- proof
  List.length_swap


-- created on 2025-05-12
-- updated on 2026-08-24

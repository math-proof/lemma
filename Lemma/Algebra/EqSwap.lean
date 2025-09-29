import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (a : List α)
  (i : ℕ) :
-- imply
  a.swap i i = a := by
-- proof
  unfold List.swap
  aesop


-- created on 2025-05-17

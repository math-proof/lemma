import stdlib.List
import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : ℕ) :
-- imply
  s.swap i i = s := by
-- proof
  unfold List.swap
  aesop


-- created on 2025-05-17

import sympy.Basic


@[main]
private lemma main
  [Decidable p]
-- given
  (h : p → (if p then
    a
  else
    b) = c) :
-- imply
  p → a = c := by
-- proof
  aesop


-- created on 2025-10-01

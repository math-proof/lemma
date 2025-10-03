import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (a : α) :
-- imply
  (s.set 0 a).tail = s.tail := by
-- proof
  aesop


-- created on 2025-07-12

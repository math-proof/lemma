import sympy.Basic


@[main, comm]
private lemma main
  [Monoid α]
-- given
  (s : List α) :
-- imply
  s.prod = s.foldr (fun a b ↦ a * b) 1 := by
-- proof
  aesop


-- created on 2025-07-15

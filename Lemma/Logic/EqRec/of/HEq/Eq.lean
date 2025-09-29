import sympy.Basic


@[main, comm 3]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h₀ : n = m)
  (h₁ : HEq a b) :
-- imply
  Eq.rec a h₀ = b := by
-- proof
  apply HEq.eq
  aesop


-- created on 2025-07-25

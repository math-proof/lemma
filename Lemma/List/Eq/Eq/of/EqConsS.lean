import sympy.Basic


@[main]
private lemma main
  {a b : List α}
-- given
  (h : a₀ :: a = b₀ :: b) :
-- imply
  a₀ = b₀ ∧ a = b := by
-- proof
  aesop


-- created on 2025-10-10

import sympy.Basic


/--
This lemma establishes the transitivity of the less-than relation in a preorder.
Given elements `a < b` and `b < c`, it concludes `a < c` by applying the transitivity property of the preorder's ordering relation.
-/
@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a < b)
  (h₁ : b < c) :
-- imply
  a < c :=
-- proof
  lt_trans h₀ h₁


-- created on 2024-11-25
-- updated on 2025-04-04

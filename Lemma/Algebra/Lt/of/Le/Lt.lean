import sympy.Basic


/--
This lemma states that in a preorder, if `a` is less than or equal to `b` (`a ≤ b`) and `b` is strictly less than `c` (`b < c`), then `a` is strictly less than `c` (`a < c`).
It demonstrates the transitivity of the strict less-than relation under the given preorder constraints.
-/
@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : b < c) :
-- imply
  a < c :=
-- proof
  lt_of_le_of_lt h₀ h₁


-- created on 2025-03-04
-- updated on 2025-04-04

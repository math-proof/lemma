import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b) :
-- imply
  x > a :=
-- proof
  h₀.left


-- created on 2026-09-26

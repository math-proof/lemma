import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b) :
-- imply
  x > a :=
-- proof
  h₀.left


-- created on 2019-06-23

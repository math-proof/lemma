import sympy.sets.sets
import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b) :
-- imply
  x ≤ b :=
-- proof
  h₀.right


-- created on 2025-03-01

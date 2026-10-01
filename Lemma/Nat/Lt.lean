import sympy.sets.sets
import sympy.Basic


@[main]
private lemma transport
  {x y a : ℝ}
-- given
  (h : x + a < y) :
-- imply
  x < y - a := by
-- proof
  linarith


@[main]
private lemma symbol.domain_defined
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Ioc a b) :
-- imply
  a < b :=
-- proof
  lt_of_lt_of_le h.1 h.2


-- created on 2019-07-06

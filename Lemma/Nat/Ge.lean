import sympy.sets.sets
import sympy.Basic


@[path]
private lemma transport
  {x y a : ℝ}
-- given
  (h : x + a ≥ y) :
-- imply
  x ≥ y - a := by
-- proof
  linarith


@[path]
private lemma symbol.domain_defined
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  b ≥ a :=
-- proof
  le_trans h.1 h.2


@[path]
private lemma simp.common_terms
  {x y a : ℝ}
-- given
  (h : x + a ≥ y + a) :
-- imply
  x ≥ y := by
-- proof
  linarith


-- created on 2019-09-03

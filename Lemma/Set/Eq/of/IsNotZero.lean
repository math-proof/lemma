import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma square_completing
  {a b c x : ℂ}
-- given
  (h : a ∈ (Set.univ : Set ℂ) \ {0}) :
-- imply
  a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (c - b ^ 2 / (4 * a)) := by
-- proof
  have ha : a ≠ 0 := h.2
  field_simp
  ring


-- created on 2023-06-30

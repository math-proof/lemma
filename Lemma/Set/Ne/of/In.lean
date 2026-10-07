import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℂ}
  {C : Set (Fin n → ℂ)}
-- given
  (h : x ∈ C \ {y}) :
-- imply
  x ≠ y := by
-- proof
  exact h.2


-- created on 2020-07-17

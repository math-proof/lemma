import sympy.vector.functions
import sympy.Basic


@[main]
private lemma main
  [Log α]
  [Div α]
  [SubNegMonoid α]
  {x y : List.Vector α n}
-- given
  (h₀ : ∀ i : Fin n, x[i] ≠ 0)
  (h₁ : ∀ i : Fin n, y[i] ≠ 0) :
-- imply
  log (x / y) = log x - log y := by
-- proof
  sorry


-- created on 2025-12-03

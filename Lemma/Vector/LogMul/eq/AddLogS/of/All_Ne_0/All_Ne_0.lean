import sympy.Basic
import sympy.vector.functions


@[main]
private lemma main
  [Log α]
  [Mul α]
  [Add α]
  [Zero α]
  {x y : List.Vector α n}
-- given
  (h₀ : ∀ i : Fin n, x[i] ≠ 0)
  (h₁ : ∀ i : Fin n, y[i] ≠ 0) :
-- imply
  log (x * y) = log x + log y := by
-- proof
  sorry


-- created on 2025-12-03

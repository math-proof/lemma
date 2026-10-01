import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ} :
-- imply
  ∑ i, x i * y i = x ⬝ᵥ y :=
-- proof
  rfl


-- created on 2026-09-27

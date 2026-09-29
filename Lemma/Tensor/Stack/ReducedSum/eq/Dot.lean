import sympy.Basic
open Matrix


@[main]
private lemma main
  {n m : ℕ}
  {A : Matrix (Fin n) (Fin m) ℝ}
  {b : Fin m → ℝ} :
-- imply
  (fun i => ∑ j, A i j * b j) = A *ᵥ b :=
-- proof
  rfl


-- created on 2026-09-27

import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[path]
private lemma main
  [CommSemiring α]
  {n : ℕ}
  {x y : Fin n → α} :
-- imply
  ∑ i, y i * x i = y ⬝ᵥ x :=
-- proof
  rfl


@[path]
private lemma arithmetic_progression
  {n k : ℕ}
  {a : Fin k → ℝ} :
-- imply
  ∑ j : Fin k, ∑ i ∈ Finset.Icc 1 n, a j * (i : ℝ) ^ (j : ℕ) =
    (fun _ : Fin k => (n : ℝ) ^ k) ⬝ᵥ (Matrix.mulVec (Matrix.of fun (j i : Fin k) => (-1 : ℝ) ^ ((j : ℤ) - i) * (Nat.choose (j + 1) i : ℝ))⁻¹ a) := by
-- proof
  -- sorry: false as transcribed from py (unproved there); k = 2 gives 3n²a₀ + 2n²a₁ on the rhs vs n·a₀ + n(n+1)/2·a₁ on the lhs
  sorry


-- created on 2020-11-18

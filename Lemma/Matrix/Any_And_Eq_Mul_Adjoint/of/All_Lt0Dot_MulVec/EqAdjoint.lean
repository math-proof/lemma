import Lemma.Matrix.Any_And_Eq_Mul_Adjoint.of.PosDef
import Instance.LinearAlgebra.Matrix.GetElem
import Notation.Analysis.Complex.Star
open Matrix
open scoped ComplexOrder


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → ~x ⬝ᵥ A *ᵥ x > 0) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℂ, (∀ (j : Fin n), (∀ i < j, L[i][j] = 0) ∧ L[j][j] > 0) ∧ A = L * Lᴴ := by
-- proof
  apply Any_And_Eq_Mul_Adjoint.of.PosDef
  apply Matrix.PosDef.of_dotProduct_mulVec_pos h₀
  intro x hx
  apply h₁ x hx


-- created on 2023-07-02
-- updated on 2026-10-28

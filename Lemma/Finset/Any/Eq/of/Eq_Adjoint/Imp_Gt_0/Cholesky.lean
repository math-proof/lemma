import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  exact hA.exists_cholesky


-- created on 2026-09-27

import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
open Matrix
open scoped ComplexOrder


@[path]
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
  exact Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA


-- created on 2023-07-02

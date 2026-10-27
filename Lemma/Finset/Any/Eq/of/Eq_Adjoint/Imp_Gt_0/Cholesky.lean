import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
import Notation.Analysis.Complex.Star
open Matrix
open scoped ComplexOrder


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ~x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
-- proof
  apply Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
  apply Matrix.PosDef.of_dotProduct_mulVec_pos h₀
  intro x hx
  apply h₁ x hx


-- created on 2023-07-02
-- updated on 2026-10-26

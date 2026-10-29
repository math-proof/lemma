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
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ~x ⬝ᵥ (A *ᵥ x)) :
-- imply
  ∃ L : Matrix (Fin n) (Fin n) ℂ, (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
-- proof
  have hA : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos h₀
    intro x hx
    apply h₁ x hx
  obtain ⟨L, htri, hEq⟩ := Any_And_Eq_Mul_Adjoint.of.PosDef hA
  refine ⟨L, ?_, ?_, hEq⟩
  ·
    intro i j hij
    simpa [getElem_getElem] using (htri j).1 i hij
  ·
    intro i
    simpa [getElem_getElem] using (htri i).2


-- created on 2023-07-02
-- updated on 2026-10-28

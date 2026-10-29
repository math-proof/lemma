import Lemma.Matrix.Any_And_Eq_Mul_Adjoint.of.PosDef
import Instance.LinearAlgebra.Matrix.GetElem
import Lemma.Matrix.Eq.of.IsCholeskyRec.IsCholeskyRec
import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
open Matrix
open scoped ComplexOrder


/-- The Cholesky recursion determines the factor: for positive definite `A`, a matrix satisfying the
recursion is lower triangular with positive diagonal and `A = L Lᴴ`. -/
@[path]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {A L : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (hA : A.PosDef)
  (h : IsCholeskyRec A L) :
-- imply
  (∀ i j, i < j → L i j = 0) ∧ (∀ i, 0 < L i i) ∧ A = L * Lᴴ := by
-- proof
  obtain ⟨L₀, htri, hL₀⟩ := Any_And_Eq_Mul_Adjoint.of.PosDef hA
  have hlow : ∀ i j, i < j → L₀ i j = 0 := fun i j hij => by
    simpa [getElem_getElem] using (htri j).1 i hij
  have hpos : ∀ i, 0 < L₀ i i := fun i => by
    simpa [getElem_getElem] using (htri i).2
  have h₀ : IsCholeskyRec A L₀ := by
    rw [hL₀]
    exact IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
  rw [Eq.of.IsCholeskyRec.IsCholeskyRec h h₀]
  exact ⟨hlow, hpos, hL₀⟩


-- created on 2026-10-07
-- updated on 2026-10-28

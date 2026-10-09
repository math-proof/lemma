import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
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
  obtain ⟨L₀, hlow, hpos, hL₀⟩ := Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA
  have h₀ : IsCholeskyRec A L₀ := by
    rw [hL₀]
    exact IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
  rw [Eq.of.IsCholeskyRec.IsCholeskyRec h h₀]
  exact ⟨hlow, hpos, hL₀⟩


-- created on 2026-10-07

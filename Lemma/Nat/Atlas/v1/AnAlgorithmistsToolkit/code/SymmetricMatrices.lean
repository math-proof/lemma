import Mathlib
import Initialize.Tactic.Attr.Basic
open Matrix


namespace SymmetricMatrixProperties

/--
[isHermitian_iff_transpose_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma isHermitian_iff_transpose_eq
  [Fintype n]
  [DecidableEq n]
  (M : Matrix n n ℝ) :
-- imply
  M.IsHermitian ↔ Mᵀ = M := by
-- proof
  unfold Matrix.IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]

end SymmetricMatrixProperties

namespace SymmetricMatrixProperties

/--
[eigenvectors_orthogonal_of_ne_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma eigenvectors_orthogonal_of_ne_eigenvalues
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
  {v w : n → ℝ}
  {μ₁ μ₂ : ℝ}
-- given
  (hM : M.IsHermitian)
  (hμ : μ₁ ≠ μ₂)
  (hv : M.mulVec v = μ₁ • v)
  (hw : M.mulVec w = μ₂ • w) :
-- imply
  dotProduct v w = 0 := by
-- proof
  have hsym : Mᵀ = M := (isHermitian_iff_transpose_eq M).mp hM
  have symm_dot : dotProduct (M *ᵥ v) w = dotProduct v (M *ᵥ w) := by
    rw [dotProduct_comm (M *ᵥ v) w, dotProduct_mulVec]
    have hvecmul : w ᵥ* M = M *ᵥ w := by
      conv_lhs => rw [← hsym]
      exact vecMul_transpose M w
    rw [hvecmul, dotProduct_comm]
  have h1 : dotProduct (M *ᵥ v) w = μ₁ * dotProduct v w := by
    rw [hv, smul_dotProduct, smul_eq_mul]
  have h2 : dotProduct v (M *ᵥ w) = μ₂ * dotProduct v w := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  have key : μ₁ * dotProduct v w = μ₂ * dotProduct v w := by linarith
  have h := sub_eq_zero.mpr key
  rw [← sub_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hμ)

end SymmetricMatrixProperties

namespace SymmetricMatrixProperties

/--
[eigenvector_linear_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma eigenvector_linear_combination
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
  {v w : n → ℝ}
  {μ : ℝ}
  (hv : M.mulVec v = μ • v)
  (hw : M.mulVec w = μ • w)
  (a b : ℝ) :
-- imply
  M.mulVec (a • v + b • w) = μ • (a • v + b • w) := by
-- proof
  rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, smul_add, smul_comm μ a, smul_comm μ b]

end SymmetricMatrixProperties

namespace SymmetricMatrixProperties

/--
[exists_orthonormalBasis_eigenvectors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma exists_orthonormalBasis_eigenvectors
  [Fintype n]
  [DecidableEq n]
  (M : Matrix n n ℝ)
-- given
  (hM : M.IsHermitian) :
-- imply
  ∃ (v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (eigvals : n → ℝ), ∀ j, M.mulVec (v j) = eigvals j • (v j) :=
-- proof
  ⟨hM.eigenvectorBasis, hM.eigenvalues, hM.mulVec_eigenvectorBasis⟩

end SymmetricMatrixProperties

namespace SymmetricMatrixProperties

/--
[eq_eigenvectorUnitary_mul_diagonal_mul_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma eq_eigenvectorUnitary_mul_diagonal_mul_transpose
  [Fintype n]
  [DecidableEq n]
  (M : Matrix n n ℝ)
-- given
  (hM : M.IsHermitian) :
-- imply
  M = (↑hM.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hM.eigenvalues * (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
-- proof
  have h := hM.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply] at h
  have hstar : (star (↑hM.eigenvectorUnitary : Matrix n n ℝ)) =
    (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hdiag : diagonal (RCLike.ofReal ∘ hM.eigenvalues) = diagonal hM.eigenvalues := by
    congr 1
  rwa [hstar, hdiag] at h

end SymmetricMatrixProperties

namespace SymmetricMatrixProperties

/--
[proposition2_symmetric_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SymmetricMatrices.lean)
-/
@[path]
lemma proposition2_symmetric_matrix
  [Fintype n]
  [DecidableEq n]
  {M : Matrix n n ℝ}
-- given
  (hM : M.IsHermitian) :
-- imply
  (∀ {v w : n → ℝ} {μ₁ μ₂ : ℝ}, μ₁ ≠ μ₂ → M.mulVec v = μ₁ • v → M.mulVec w = μ₂ • w → dotProduct v w = 0) ∧ (∀ {v w : n → ℝ} {μ : ℝ}, M.mulVec v = μ • v → M.mulVec w = μ • w → ∀ a b : ℝ, M.mulVec (a • v + b • w) = μ • (a • v + b • w)) ∧ (∃ (v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) (eigvals : n → ℝ), ∀ j, M.mulVec (v j) = eigvals j • (v j)) ∧ (M = (↑hM.eigenvectorUnitary : Matrix n n ℝ) * Matrix.diagonal hM.eigenvalues * (↑hM.eigenvectorUnitary : Matrix n n ℝ)ᵀ) :=
-- proof
  ⟨fun hμ hv hw => eigenvectors_orthogonal_of_ne_eigenvalues hM hμ hv hw,
    fun hv hw a b => eigenvector_linear_combination hv hw a b,
    exists_orthonormalBasis_eigenvectors M hM,
    eq_eigenvectorUnitary_mul_diagonal_mul_transpose M hM⟩

end SymmetricMatrixProperties


-- created on 2026-10-23

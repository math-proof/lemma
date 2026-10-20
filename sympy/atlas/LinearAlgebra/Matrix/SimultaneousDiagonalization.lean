/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix.PosDef

/-!
# Simultaneous diagonalization by congruence

This file normalizes a real positive-definite matrix to the identity and simultaneously
diagonalizes a real symmetric matrix by the same invertible congruence.
-/

namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem simulDiag_invSqrt_sq (x : ℝ) (hx : 0 < x) :
    (√x)⁻¹ * x * (√x)⁻¹ = 1 := by
  have hsqrt : √x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  field_simp [hsqrt]
  exact (Real.sq_sqrt hx.le).symm

omit [DecidableEq n] in
private theorem simulDiag_isSymm_congr {S : Matrix n n ℝ} (Q : Matrix n n ℝ)
    (hS : S.IsSymm) : (Matrix.transpose Q * S * Q).IsSymm := by
  simpa using (Matrix.isHermitian_conjTranspose_mul_mul Q
    (Matrix.isHermitian_iff_isSymm.mpr hS)).isSymm

/-- A real positive-definite matrix is congruent to the identity by an invertible matrix. -/
theorem _root_.Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one
    {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ Q : Matrix n n ℝ, IsUnit Q ∧ Matrix.transpose Q * P * Q = 1 := by
  let U : Matrix.unitaryGroup n ℝ := hP.isHermitian.eigenvectorUnitary
  let d : n → ℝ := fun i => (√(hP.isHermitian.eigenvalues i))⁻¹
  have hU : Matrix.transpose (U : Matrix n n ℝ) * U = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hspec : P =
      (U : Matrix n n ℝ) * Matrix.diagonal hP.isHermitian.eigenvalues *
        Matrix.transpose (U : Matrix n n ℝ) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hP.isHermitian.spectral_theorem
  refine ⟨(U : Matrix n n ℝ) * Matrix.diagonal d, ?_, ?_⟩
  · refine Unitary.isUnit_coe.mul (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => ?_))
    exact isUnit_iff_ne_zero.mpr <| inv_ne_zero <|
      ne_of_gt <| Real.sqrt_pos.2 <| hP.eigenvalues_pos i
  · calc
      Matrix.transpose ((U : Matrix n n ℝ) * Matrix.diagonal d) * P *
          ((U : Matrix n n ℝ) * Matrix.diagonal d) =
          Matrix.diagonal d * (Matrix.transpose (U : Matrix n n ℝ) * U) *
            Matrix.diagonal hP.isHermitian.eigenvalues *
              (Matrix.transpose (U : Matrix n n ℝ) * U) * Matrix.diagonal d := by
            rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
            conv_lhs =>
              lhs
              rhs
              rw [hspec]
            noncomm_ring
      _ = Matrix.diagonal d * Matrix.diagonal hP.isHermitian.eigenvalues *
          Matrix.diagonal d := by rw [hU]; simp
      _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
        simpa [d] using congrArg Matrix.diagonal <|
          funext fun i => simulDiag_invSqrt_sq _ (hP.eigenvalues_pos i)

private theorem simulDiag_isSymm_orthogonal_diagonalization {M : Matrix n n ℝ}
    (hM : M.IsSymm) :
    ∃ W : Matrix n n ℝ,
      IsUnit W ∧ (Matrix.transpose W * M * W).IsDiag ∧ Matrix.transpose W * W = 1 := by
  let hH : M.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hM
  let W : Matrix.unitaryGroup n ℝ := hH.eigenvectorUnitary
  have hdiag : Matrix.transpose (W : Matrix n n ℝ) * M * W =
      Matrix.diagonal hH.eigenvalues := by
    simpa [W, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨W, Unitary.isUnit_coe, ?_, ?_⟩
  · rw [hdiag]
    exact Matrix.isDiag_diagonal _
  · simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self W

/--
Simultaneous diagonalization of two real quadratic forms with one positive-definite: for a
symmetric matrix `S` and a positive-definite matrix `P`, there is an invertible congruence
diagonalizing `S` while normalizing `P` to the identity.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Endomorphisms / simultaneous diagonalization of two real quadratic forms, with one
positive-definite; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University
Press (2013), Theorem 4.5.15.

Proves `Wanted` entry `simultaneous_diagonalization_posDef`.

Proof: Normalize `P` to the identity by a congruence built from its orthonormal eigenbasis, scaled
by the inverse square roots of its eigenvalues, then orthogonally diagonalize the transformed
symmetric matrix. This is the argument of Wikipedia's "Definite matrix", section "Simultaneous
diagonalization", with the eigenbasis scaling in place of a Cholesky factor.
-/
theorem simultaneous_diagonalization_posDef
    (S P : Matrix n n ℝ) (hS : S.IsSymm) (hP : P.PosDef) :
    ∃ C : Matrix n n ℝ,
      IsUnit C ∧ (Matrix.transpose C * S * C).IsDiag ∧ Matrix.transpose C * P * C = 1 := by
  obtain ⟨Q, hQ, hQP⟩ := hP.exists_isUnit_transpose_mul_mul_eq_one
  obtain ⟨W, hW, hdiag, hWW⟩ :=
    simulDiag_isSymm_orthogonal_diagonalization (simulDiag_isSymm_congr Q hS)
  refine ⟨Q * W, hQ.mul hW, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using hdiag
  · calc
      Matrix.transpose (Q * W) * P * (Q * W) =
          Matrix.transpose W * (Matrix.transpose Q * P * Q) * W := by
            rw [Matrix.transpose_mul]
            noncomm_ring
      _ = Matrix.transpose W * W := by rw [hQP]; simp
      _ = 1 := hWW

end MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

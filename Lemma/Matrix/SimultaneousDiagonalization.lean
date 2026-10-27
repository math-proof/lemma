import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

variable [Fintype n] [DecidableEq n]
/--
[simulDiag_invSqrt_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
private lemma simulDiag_invSqrt_sq (x : ℝ) (hx : 0 < x) :
  (√x)⁻¹ * x * (√x)⁻¹ = 1 := by
  have hsqrt : √x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  field_simp [hsqrt]
  exact (Real.sq_sqrt hx.le).symm

end MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

variable [Fintype n] [DecidableEq n]
/--
[simulDiag_isSymm_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
omit [DecidableEq n] in
private lemma simulDiag_isSymm_congr {S : Matrix n n ℝ} (Q : Matrix n n ℝ)
  (hS : S.IsSymm) : (Matrix.transpose Q * S * Q).IsSymm := by
  simpa using (Matrix.isHermitian_conjTranspose_mul_mul Q
    (Matrix.isHermitian_iff_isSymm.mpr hS)).isSymm

end MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

variable [Fintype n] [DecidableEq n]
/--
[exists_isUnit_transpose_mul_mul_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
lemma _root_.Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one
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

end MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

variable [Fintype n] [DecidableEq n]
/--
[simulDiag_isSymm_orthogonal_diagonalization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
private lemma simulDiag_isSymm_orthogonal_diagonalization {M : Matrix n n ℝ}
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

end MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

namespace MathlibExt.LinearAlgebra.Matrix.SimultaneousDiagonalizationWanted

/--
[simultaneous_diagonalization_posDef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
lemma simultaneous_diagonalization_posDef
  [Fintype n] [DecidableEq n]
  {S P : Matrix n n ℝ}
-- given
  (hS : S.IsSymm)
  (hP : P.PosDef) :
-- imply
  ∃ C : Matrix n n ℝ,
    IsUnit C ∧ (Matrix.transpose C * S * C).IsDiag ∧ Matrix.transpose C * P * C = 1 := by
-- proof
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

/--
[_root_.Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/SimultaneousDiagonalization.lean)
-/
@[path]
private lemma Matrix_PosDef_exists_isUnit_transpose_mul_mul_eq_one_eq
  [Fintype n] [DecidableEq n]
  {P : Matrix n n ℝ}
-- given
  (hP : P.PosDef) :
-- imply
  ∃ Q : Matrix n n ℝ, IsUnit Q ∧ Matrix.transpose Q * P * Q = 1 := by
-- proof
  apply Matrix.PosDef.exists_isUnit_transpose_mul_mul_eq_one hP


-- created on 2026-10-20
-- updated on 2026-10-26

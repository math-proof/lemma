import Mathlib
import sympy.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
open Module FiniteDimensional


namespace SymplecticLinearAlgebra

/--
[symplectic_even_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticEvenDim.lean)
-/
@[path]
lemma symplectic_even_dim
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  Even (finrank ℝ V) := by
-- proof
  set n := finrank ℝ V
  set b := finBasis ℝ V
  set M := LinearMap.BilinForm.toMatrix b Ω
  have hskew : M.transpose = -M := by
    ext i j
    simp only [M, LinearMap.BilinForm.toMatrix_apply, Matrix.transpose_apply, Matrix.neg_apply]
    exact sympl_skew hΩ.alt (b j) (b i)
  have hNondeg : Ω.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hΩ.alt.isRefl).mpr hΩ.nondeg
  have hdet : M.det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hNondeg
  have key : M.det = (-1 : ℝ) ^ n * M.det := by
    calc M.det = M.transpose.det := (Matrix.det_transpose M).symm
    _ = (-M).det := by rw [hskew]
    _ = (-1) ^ Fintype.card (Fin n) * M.det := Matrix.det_neg M
    _ = (-1 : ℝ) ^ n * M.det := by rw [Fintype.card_fin]
  have h6 : (-1 : ℝ) ^ n = 1 := by
    have : (-1 : ℝ) ^ n * M.det = 1 * M.det := by linarith
    exact mul_right_cancel₀ hdet this
  rwa [neg_one_pow_eq_one_iff_even] at h6
  norm_num

end SymplecticLinearAlgebra


-- created on 2026-10-23

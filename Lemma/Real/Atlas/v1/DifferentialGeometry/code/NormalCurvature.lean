import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.NormalCurvature
open Matrix Finset BigOperators


/--
[normalCurvature_denom_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/NormalCurvature.lean)
-/
@[path]
lemma normalCurvature_denom_pos
  {n : ℕ}
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ}
  {X : Fin n → ℝ}
-- given
  (hx : x ∈ patch.domain)
  (hX : X ≠ 0) :
-- imply
  (0 : ℝ) < X ⬝ᵥ (firstFundamentalForm patch x).mulVec X := by
-- proof
  have hG := firstFundamentalForm_posDef patch x hx
  have h := hG.dotProduct_mulVec_pos (x := X) hX
  simp only [star_trivial] at h
  exact h

/--
[normalCurvature_eq_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/NormalCurvature.lean)
-/
@[path]
lemma normalCurvature_eq_ratio
  {n : ℕ}
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ}
  {X : Fin n → ℝ}
-- given
  (hx : x ∈ patch.domain) :
-- imply
  normalCurvature patch x X = (X ⬝ᵥ (firstFundamentalForm patch x).mulVec ((shapeOperator patch x).mulVec X)) / (X ⬝ᵥ (firstFundamentalForm patch x).mulVec X) := by
-- proof
  unfold normalCurvature
  congr 1
  congr 1
  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  unfold shapeOperator
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]


-- created on 2026-10-23

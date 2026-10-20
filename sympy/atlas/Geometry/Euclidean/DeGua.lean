/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGua.lean -/

import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped InnerProductSpace

namespace MetaMathlibExt

/-- De Gua's theorem (statement `degua-s1`): a trirectangular tetrahedron with legs `u`,
  `v`, `w` (mutually orthogonal edges from one vertex, via inner-product zeros) satisfies
  Area(hypotenuse face)^2 = Area1^2 + Area2^2 + Area3^2. The right-face areas are
  half-products of leg norms; the hypotenuse-face area is the genuine 2D triangular area
  via the Gram determinant (Lagrange identity for half the cross-product norm), not a
  vacuous 3D volume. Source: https://en.wikipedia.org/wiki/De_Gua%27s_theorem
Proves `Wanted` entry `deGua`.
-/
theorem deGua : ∀ (u v w : EuclideanSpace ℝ (Fin 3)),
  ⟪u, v⟫_ℝ = 0 →
  ⟪u, w⟫_ℝ = 0 →
  ⟪v, w⟫_ℝ = 0 →
  ∀ (Auv Auw Avw Ahyp : ℝ),
  Auv = ‖u‖ * ‖v‖ / 2 →
  Auw = ‖u‖ * ‖w‖ / 2 →
  Avw = ‖v‖ * ‖w‖ / 2 →
  (2 * Ahyp) ^ 2 = ‖u - v‖ ^ 2 * ‖u - w‖ ^ 2 - (⟪u - v, u - w⟫_ℝ) ^ 2 →
  Ahyp ^ 2 = Auv ^ 2 + Auw ^ 2 + Avw ^ 2 := by
  intro u v w huv huw hvw Auv Auw Avw Ahyp hAuv hAuw hAvw hHyp
  have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huv
  have h1 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, huv]; ring
  have h2 : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [norm_sub_sq_real, huw]; ring
  have h3 : ⟪u - v, u - w⟫_ℝ = ‖u‖ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, huw, hvu, hvw]
    ring
  rw [h1, h2, h3] at hHyp
  rw [hAuv, hAuw, hAvw]
  linear_combination hHyp / 4

end MetaMathlibExt

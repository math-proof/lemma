import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped InnerProductSpace


namespace MetaMathlibExt

/--
[deGua](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGua.lean)
-/
@[path]
lemma deGua
  :
-- imply
  ∀ (u v w : EuclideanSpace ℝ (Fin 3)),
  ⟪u, v⟫_ℝ = 0 →
  ⟪u, w⟫_ℝ = 0 →
  ⟪v, w⟫_ℝ = 0 →
  ∀ (Auv Auw Avw Ahyp : ℝ),
  Auv = ‖u‖ * ‖v‖ / 2 →
  Auw = ‖u‖ * ‖w‖ / 2 →
  Avw = ‖v‖ * ‖w‖ / 2 →
  (2 * Ahyp) ^ 2 = ‖u - v‖ ^ 2 * ‖u - w‖ ^ 2 - (⟪u - v, u - w⟫_ℝ) ^ 2 →
  Ahyp ^ 2 = Auv ^ 2 + Auw ^ 2 + Avw ^ 2 := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26

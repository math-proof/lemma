import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.DeGua
open scoped InnerProductSpace
open MetaMathlibExt


/--
[deGua](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/DeGua.lean)
-/
@[path]
private lemma deGua_eq
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
  apply MetaMathlibExt.deGua


-- created on 2026-10-20

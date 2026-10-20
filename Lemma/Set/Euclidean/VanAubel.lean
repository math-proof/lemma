import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.VanAubel
open scoped InnerProductSpace
open MetaMathlibExt


/--
[vanAubel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanAubel.lean)
-/
@[path]
private lemma vanAubel_eq
  :
-- imply
  ∀ (A B C D : EuclideanSpace ℝ (Fin 2))
      (Oab Obc Ocd Oda : EuclideanSpace ℝ (Fin 2)),
      Oab = (2 : ℝ)⁻¹ • (A + B) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((B - A).ofLp 1), ((B - A).ofLp 0)]) →
      Obc = (2 : ℝ)⁻¹ • (B + C) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((C - B).ofLp 1), ((C - B).ofLp 0)]) →
      Ocd = (2 : ℝ)⁻¹ • (C + D) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((D - C).ofLp 1), ((D - C).ofLp 0)]) →
      Oda = (2 : ℝ)⁻¹ • (D + A) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![-((A - D).ofLp 1), ((A - D).ofLp 0)]) →
      ‖Oab - Ocd‖ = ‖Obc - Oda‖ ∧ ⟪Oab - Ocd, Obc - Oda⟫_ℝ = 0 := by
-- proof
  apply MetaMathlibExt.vanAubel

/--
[vanAubel_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanAubel.lean)
-/
@[path]
private lemma vanAubel_right_eq
  :
-- imply
  ∀ (A B C D : EuclideanSpace ℝ (Fin 2))
      (Oab Obc Ocd Oda : EuclideanSpace ℝ (Fin 2)),
      Oab = (2 : ℝ)⁻¹ • (A + B) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((B - A).ofLp 1), -((B - A).ofLp 0)]) →
      Obc = (2 : ℝ)⁻¹ • (B + C) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((C - B).ofLp 1), -((C - B).ofLp 0)]) →
      Ocd = (2 : ℝ)⁻¹ • (C + D) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((D - C).ofLp 1), -((D - C).ofLp 0)]) →
      Oda = (2 : ℝ)⁻¹ • (D + A) +
        (2 : ℝ)⁻¹ • WithLp.toLp 2 (![((A - D).ofLp 1), -((A - D).ofLp 0)]) →
      ‖Oab - Ocd‖ = ‖Obc - Oda‖ ∧ ⟪Oab - Ocd, Obc - Oda⟫_ℝ = 0 := by
-- proof
  apply MetaMathlibExt.vanAubel_right


-- created on 2026-10-20

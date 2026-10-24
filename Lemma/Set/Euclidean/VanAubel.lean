import Mathlib
import sympy.Basic
open scoped InnerProductSpace


namespace MetaMathlibExt

/--
[vanAubel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanAubel.lean)
-/
@[path]
lemma vanAubel
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
  intro A B C D Oab Obc Ocd Oda h1 h2 h3 h4
  subst h1
  subst h2
  subst h3
  subst h4
  constructor
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  · rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec2_dotProduct]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_add, Fin.isValue, PiLp.sub_apply, neg_sub,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.star_apply,
      star_trivial, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[vanAubel_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/VanAubel.lean)
-/
@[path]
lemma vanAubel_right
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
  intro A B C D Oab Obc Ocd Oda h1 h2 h3 h4
  subst h1
  subst h2
  subst h3
  subst h4
  constructor
  · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp
    ring
  · rw [EuclideanSpace.inner_eq_star_dotProduct, Matrix.vec2_dotProduct]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, smul_add, Fin.isValue, PiLp.sub_apply, neg_sub,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Pi.star_apply,
      star_trivial, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23

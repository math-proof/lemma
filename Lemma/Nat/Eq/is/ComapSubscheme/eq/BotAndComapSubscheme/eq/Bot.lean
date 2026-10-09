import Mathlib
import sympy.Basic

open AlgebraicGeometry CategoryTheory

/--
[AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_eq_iff_comap_subschemeInclusion_eq_bot.lean)
-/
@[path]
private lemma main
  {W : Scheme.{u}}
  {I₁ I₂ : W.IdealSheafData} :
-- imply
  I₁ = I₂ ↔ I₂.comap I₁.subschemeι = ⊥ ∧ I₁.comap I₂.subschemeι = ⊥ := by
-- proof
  have key : ∀ (I J : W.IdealSheafData), J.comap I.subschemeι = ⊥ ↔ J ≤ I := by
    intro I J
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.ker_subschemeι]
  rw [key, key, le_antisymm_iff, and_comm]


-- created on 2026-10-05

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Def.Analysis.CStarAlgebra.Stinespring.Part8


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

theorem stinespringV0_apply (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    stinespringV0 A H φ x = StinespringPre.toPre A H φ (Finsupp.single 1 x) := by
  simp only [stinespringV0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Finsupp.lsingle_apply]

theorem stinespringV0_bound (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (x : H) :
    ‖stinespringV0 A H φ x‖ ≤ Real.sqrt ‖φ 1‖ * ‖x‖ := by
  have e1 : ‖stinespringV0 A H φ x‖ ^ 2 = RCLike.re ⟪x, φ 1 x⟫_ℂ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), stinespringV0_apply,
      stinespring_pre_inner_single, star_one, mul_one]
  have hle : RCLike.re ⟪x, φ 1 x⟫_ℂ ≤ ‖φ 1‖ * ‖x‖ ^ 2 := by
    calc RCLike.re ⟪x, φ 1 x⟫_ℂ ≤ ‖x‖ * ‖(φ 1) x‖ :=
          le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
      _ ≤ ‖x‖ * (‖φ 1‖ * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = ‖φ 1‖ * ‖x‖ ^ 2 := by ring
  have h2 : ‖stinespringV0 A H φ x‖ ^ 2 ≤ ‖φ 1‖ * ‖x‖ ^ 2 := e1.symm ▸ hle
  have h3 : ‖stinespringV0 A H φ x‖ ^ 2 ≤ (Real.sqrt ‖φ 1‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
    exact h2
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp h3

end MetaMathlibExt.Stinespring
end

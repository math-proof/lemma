import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
open Manifold MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted MathlibExtTest MathlibExtTest.Geometry MathlibExtTest.Geometry.Manifold MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv
open scoped Topology ContDiff
open MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted


namespace MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv

/--
[circle_isImmersionAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean)
-/
@[path]
lemma circle_isImmersionAt
  {t₀ : ℝ} :
-- imply
  IsImmersionAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => (Real.cos t, Real.sin t)) t₀ := by
-- proof
  apply immersionAt_of_injective_mfderiv (n := ∞) (by simp)
  · exact Filter.Eventually.of_forall fun _ =>
    contMDiffAt_iff_contDiffAt.mpr
      (Real.contDiff_cos.contDiffAt.prodMk Real.contDiff_sin.contDiffAt)
  · have hcircle :=
    (Real.hasDerivAt_cos t₀).hasFDerivAt.prodMk
      (Real.hasDerivAt_sin t₀).hasFDerivAt
    rw [mfderiv_eq_fderiv, hcircle.fderiv]
    intro u v huv
    change ℝ at u v
    change (u : ℝ) = v
    have hsin := congrArg Prod.fst huv
    have hcos := congrArg Prod.snd huv
    change u * (-Real.sin t₀) = v * (-Real.sin t₀) at hsin
    change u * Real.cos t₀ = v * Real.cos t₀ at hcos
    by_cases hs : Real.sin t₀ = 0
    · have hc : Real.cos t₀ ≠ 0 := by
      intro hc
      have htrig := Real.sin_sq_add_cos_sq t₀
      rw [hs, hc] at htrig
      norm_num at htrig
      exact mul_right_cancel₀ hc hcos
    · exact mul_right_cancel₀ (neg_ne_zero.mpr hs) hsin

end MathlibExtTest.Geometry.Manifold.ImmersionOfInjectiveMFDeriv


-- created on 2026-10-23

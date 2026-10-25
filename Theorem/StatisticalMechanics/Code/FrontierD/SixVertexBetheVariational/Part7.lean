/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem differentiable_sixVertexBethePairOneForm
    {c : ℝ} (hc : 2 < c) :
    Differentiable ℝ (sixVertexBethePairOneForm c) := by
  unfold sixVertexBethePairOneForm
  fun_prop

theorem fderiv_sixVertexBethePairOneForm_symmetric
    {c : ℝ} (hc : 2 < c) (xy u v : ℝ × ℝ) :
    fderiv ℝ (sixVertexBethePairOneForm c) xy u v =
      fderiv ℝ (sixVertexBethePairOneForm c) xy v u := by
  let ω := sixVertexBethePairOneForm c
  have hω : DifferentiableAt ℝ ω xy :=
    differentiable_sixVertexBethePairOneForm hc xy
  have hcross₁ : fderiv ℝ ω xy (1, 0) (0, 1) =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c xy.1 xy.2 := by
    have hpath := (hasDerivAt_id xy.1).prodMk
      (hasDerivAt_const xy.1 xy.2)
    have hcomp := hω.hasFDerivAt.comp_hasDerivAt xy.1 hpath
    have heval := (ContinuousLinearMap.apply ℝ ℝ (0, 1)).hasFDerivAt.comp
      xy hω.hasFDerivAt
    have hline : HasDerivAt
        (fun t => ω (t, xy.2) (0, 1))
        (fderiv ℝ ω xy (1, 0) (0, 1)) xy.1 := by
      exact heval.comp_hasDerivAt xy.1 hpath
    apply hline.unique
    convert hasDerivAt_sixVertexNormalizedTheta_right hc xy.2 xy.1 using 1
    · funext t
      simp [ω, sixVertexBethePairOneForm]
    · rw [sixVertexThetaDerivativeDenominator_swap]
  have hcross₂ : fderiv ℝ ω xy (0, 1) (1, 0) =
      (-4 * sixVertexDelta c) /
        sixVertexThetaDerivativeDenominator c xy.1 xy.2 := by
    have hpath := (hasDerivAt_const xy.2 xy.1).prodMk
      (hasDerivAt_id xy.2)
    have heval := (ContinuousLinearMap.apply ℝ ℝ (1, 0)).hasFDerivAt.comp
      xy hω.hasFDerivAt
    have hline : HasDerivAt
        (fun t => ω (xy.1, t) (1, 0))
        (fderiv ℝ ω xy (0, 1) (1, 0)) xy.2 := by
      exact heval.comp_hasDerivAt xy.2 hpath
    apply hline.unique
    simpa [ω, sixVertexBethePairOneForm] using
      hasDerivAt_sixVertexNormalizedTheta_right hc xy.1 xy.2
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  have hu : (u₁, u₂) = u₁ • (1, 0) + u₂ • (0, 1) := by ext <;> simp
  have hv : (v₁, v₂) = v₁ • (1, 0) + v₂ • (0, 1) := by ext <;> simp
  rw [hu, hv]
  simp only [map_add, map_smul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [hcross₁, hcross₂]
  ring


theorem exists_sixVertexBethePairPotential {c : ℝ} (hc : 2 < c) :
    ∃ H : (ℝ × ℝ) → ℝ, ∀ xy,
      HasFDerivAt H (sixVertexBethePairOneForm c xy) xy := by
  obtain ⟨H, hH⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    (ω := sixVertexBethePairOneForm c)
    (convex_univ : Convex ℝ (Set.univ : Set (ℝ × ℝ))) isOpen_univ
    (differentiable_sixVertexBethePairOneForm hc).differentiableOn
    (fun xy _ u v => fderiv_sixVertexBethePairOneForm_symmetric hc xy u v)
  exact ⟨H, fun xy => hH xy (Set.mem_univ xy)⟩


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/BetaCMatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
open scoped BigOperators
open Real Filter Topology Set Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS.BetaCMatch

open StatMech.OSSS.IntegrationSubcritical

open StatMech.OSSS.BetaThresholdBound


theorem bcm_expBound_tendsto_zero (M Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => M * Real.exp (-(((n : ℝ) / Q) * δ))) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = M * 0 by ring]
  apply Tendsto.const_mul
  apply Real.tendsto_exp_atBot.comp
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) / Q) * δ) atTop atTop := by
    apply Filter.Tendsto.atTop_mul_const hδ
    apply Filter.Tendsto.atTop_div_const hQ
    exact tendsto_natCast_atTop_atTop
  exact tendsto_neg_atBot_iff.mpr h1


theorem bcm_theta_zero_of_decay (θ M Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ)
    (hθnn : 0 ≤ θ)
    (hbound : ∀ n : ℕ, θ ≤ M * Real.exp (-(((n : ℝ) / Q) * δ))) :
    θ = 0 := by
  have hb0 := bcm_expBound_tendsto_zero M Q δ hQ hδ
  have hconst : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ) := tendsto_const_nhds
  have hle : θ ≤ 0 := le_of_tendsto_of_tendsto hconst hb0 (Eventually.of_forall hbound)
  linarith


theorem bcm_theta_pos_of_meanField (θ f β₁ β : ℝ)
    (hθf : θ = f) (hmf : β - β₁ ≤ f) (hlt : β₁ < β) : 0 < θ := by
  rw [hθf]
  have : 0 < β - β₁ := by linarith
  linarith


end OSSS.BetaCMatch
end StatMech

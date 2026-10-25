/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part5


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical D hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  amplitude := h.amplitude
  amplitude_pos := h.amplitude_pos
  relativePrefactor := h.relativePrefactor
  relativePrefactor_tendsto_one := h.relativePrefactor_tendsto_one
  mass_scaling := by
    intro β hβ
    simpa [hpred] using h.mass_scaling β hβ

end FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass := by
  classical
  let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
  have hrelpos :
      ∀ᶠ β in L, 0 < hasymp.relativePrefactor β := by
    have hdist :=
      (Metric.tendsto_nhds.mp hasymp.relativePrefactor_tendsto_one)
        ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hdist] with β hβ
    rw [Real.dist_eq] at hβ
    have hbounds := abs_sub_lt_iff.mp hβ
    linarith
  let posWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hposWindow_spec :
      0 < posWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - posWindow) (Ising.betaC 3) →
          0 < hasymp.relativePrefactor β := by
    simpa [posWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hprefLog :
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (hasymp.amplitude * hasymp.relativePrefactor β) /
            Real.log (Ising.betaC 3 - β))
        L (nhds 0) := by
    have hpref :
        Filter.Tendsto
          (fun β : ℝ => hasymp.amplitude * hasymp.relativePrefactor β)
          L (nhds hasymp.amplitude) := by
      simpa using
        (tendsto_const_nhds.mul hasymp.relativePrefactor_tendsto_one)
    have hlogpref :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hasymp.amplitude * hasymp.relativePrefactor β))
          L (nhds (Real.log hasymp.amplitude)) :=
      (Real.continuousAt_log hasymp.amplitude_pos.ne').tendsto.comp hpref
    have hlogd :
        Filter.Tendsto (fun β : ℝ => Real.log (Ising.betaC 3 - β))
          L Filter.atBot := by
      simpa [L, Ising3DModel] using tendsto_log_betaC_sub_atBot Ising3DModel
    exact hlogpref.div_atBot hlogd
  exact
    { δ := min hasymp.δ posWindow
      δ_pos := lt_min hasymp.δ_pos hposWindow_spec.1
      δ_le_betaC := by
        exact le_trans (min_le_left hasymp.δ posWindow) hasymp.δ_le_betaC
      massPrefactor := fun β =>
        hasymp.amplitude * hasymp.relativePrefactor β
      massPrefactor_pos := by
        intro β hβ
        have hβPos :
            β ∈ Set.Ioo (Ising.betaC 3 - posWindow) (Ising.betaC 3) := by
          constructor
          · linarith [hβ.1, min_le_right hasymp.δ posWindow]
          · exact hβ.2
        exact mul_pos hasymp.amplitude_pos (hposWindow_spec.2 β hβPos)
      massPrefactor_log_negligible := by
        simpa [L] using hprefLog
      mass_scaling := by
        intro β hβ
        have hβAsymp :
            β ∈ Set.Ioo (Ising.betaC 3 - hasymp.δ) (Ising.betaC 3) := by
          constructor
          · linarith [hβ.1, min_le_left hasymp.δ posWindow]
          · exact hβ.2
        simpa [mul_assoc] using hasymp.mass_scaling β hβAsymp }

end Exact3D
end StatMech

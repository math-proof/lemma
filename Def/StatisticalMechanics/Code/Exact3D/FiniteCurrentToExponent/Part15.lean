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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
      D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  amplitude := h.amplitude
  amplitude_pos := h.amplitude_pos
  relativePrefactor := h.relativePrefactor
  relativePrefactor_tendsto_one := h.relativePrefactor_tendsto_one
  mass_scaling := by
    intro p hp
    simpa [hpred] using h.mass_scaling p hp

end FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass := by
  classical
  let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
  have hrelpos :
      ∀ᶠ p in L, 0 < hasymp.relativePrefactor p := by
    have hdist :=
      (Metric.tendsto_nhds.mp hasymp.relativePrefactor_tendsto_one)
        ((1 : ℝ) / 2) (by norm_num)
    filter_upwards [hdist] with p hp
    rw [Real.dist_eq] at hp
    have hbounds := abs_sub_lt_iff.mp hp
    linarith
  let posWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hposWindow_spec :
      0 < posWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - posWindow) Ising3DFKPC →
          0 < hasymp.relativePrefactor p := by
    simpa [posWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hrelpos)
  have hprefLog :
      Filter.Tendsto
        (fun p : ℝ =>
          Real.log (hasymp.amplitude * hasymp.relativePrefactor p) /
            Real.log (Ising3DFKPC - p))
        L (nhds 0) := by
    have hpref :
        Filter.Tendsto
          (fun p : ℝ => hasymp.amplitude * hasymp.relativePrefactor p)
          L (nhds hasymp.amplitude) := by
      simpa using
        (tendsto_const_nhds.mul hasymp.relativePrefactor_tendsto_one)
    have hlogpref :
        Filter.Tendsto
          (fun p : ℝ =>
            Real.log (hasymp.amplitude * hasymp.relativePrefactor p))
          L (nhds (Real.log hasymp.amplitude)) :=
      (Real.continuousAt_log hasymp.amplitude_pos.ne').tendsto.comp hpref
    have hlogd :
        Filter.Tendsto (fun p : ℝ => Real.log (Ising3DFKPC - p))
          L Filter.atBot := by
      simpa [L, ParameterModel] using
        tendsto_log_betaC_sub_atBot (ParameterModel Ising3DFKPC)
    exact hlogpref.div_atBot hlogd
  exact
    { pδ := min hasymp.pδ posWindow
      pδ_pos := lt_min hasymp.pδ_pos hposWindow_spec.1
      massPrefactor := fun p => hasymp.amplitude * hasymp.relativePrefactor p
      massPrefactor_pos := by
        intro p hp
        have hpPos :
            p ∈ Set.Ioo (Ising3DFKPC - posWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hasymp.pδ posWindow]
          · exact hp.2
        exact mul_pos hasymp.amplitude_pos (hposWindow_spec.2 p hpPos)
      massPrefactor_log_negligible := by
        simpa [L] using hprefLog
      mass_scaling := by
        intro p hp
        have hpAsymp :
            p ∈ Set.Ioo (Ising3DFKPC - hasymp.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hasymp.pδ posWindow]
          · exact hp.2
        simpa [mul_assoc] using hasymp.mass_scaling p hpAsymp }

end Exact3D
end StatMech

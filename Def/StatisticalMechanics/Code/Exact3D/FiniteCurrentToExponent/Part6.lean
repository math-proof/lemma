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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part6


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hexact :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass where
  δ := hexact.δ
  δ_pos := hexact.δ_pos
  δ_le_betaC := hexact.δ_le_betaC
  logRemainder := fun β => Real.log (hexact.massPrefactor β)
  mass_pos := by
    intro β hβ
    rw [hexact.mass_scaling β hβ]
    exact mul_pos (hexact.massPrefactor_pos β hβ) (Real.exp_pos _)
  logRemainder_negligible := hexact.massPrefactor_log_negligible
  log_mass_scaling := by
    intro β hβ
    have hpref_pos : 0 < hexact.massPrefactor β :=
      hexact.massPrefactor_pos β hβ
    have hpref_ne : hexact.massPrefactor β ≠ 0 := hpref_pos.ne'
    have hexp_ne :
        Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [hexact.mass_scaling β hβ, Real.log_mul hpref_ne hexp_ne,
      Real.log_exp]
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
    C hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hlog.δ
  δ_pos := hlog.δ_pos
  δ_le_betaC := hlog.δ_le_betaC
  mass_pos := hlog.mass_pos
  log_mass_ratio_tendsto := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hlimit :
        Filter.Tendsto
          (fun β : ℝ =>
            C.predictedExponent +
              hlog.logRemainder β / Real.log (Ising.betaC 3 - β))
          L (nhds C.predictedExponent) := by
      simpa [L] using tendsto_const_nhds.add hlog.logRemainder_negligible
    refine Filter.Tendsto.congr' ?_ hlimit
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising.betaC 3 - hlog.δ < Ising.betaC 3 by
          linarith [hlog.δ_pos]),
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - (1 : ℝ) < Ising.betaC 3 by norm_num)]
      with β hβδ hβone
    have hdiff : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβone.1, hβone.2]
    have hden : Real.log (Ising.betaC 3 - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      C.predictedExponent +
          hlog.logRemainder β / Real.log (Ising.betaC 3 - β) =
        Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β)
    rw [hlog.log_mass_scaling β hβδ]
    field_simp [hden]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hexact :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_logAffineNearCritical
    C hmass
    (freePositiveSubcriticalMassLogAffineNearCritical_of_exactPowerLaw
      C hmass hexact)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_exactPowerLaw
    C hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

end Exact3D
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part10


namespace StatMech

namespace Exact3D

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def toFKMassTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKMassAnalyticRGToExponentTarget C where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMass_pos := fun p hp => T.fkMass_pos hp
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  fkPrefactor := fun p => (T.fkMassPrefactor p)⁻¹
  fkPrefactor_pos := fun p hp => inv_pos.mpr (T.fkMassPrefactor_pos p hp)
  fkPrefactor_log_negligible := by
    refine tendsto_log_inv_prefactor_div_log_betaC_sub
      (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))) ?_ ?_
    · filter_upwards
        [Ioo_mem_nhdsLT
          (show (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC -
              T.pδ <
            (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3))).betaC by
            rw [ParameterModel]
            linarith [T.pδ_pos])] with p hp
      exact T.fkMassPrefactor_pos p (by simpa [ParameterModel] using hp)
    · simpa [ParameterModel] using T.fkMassPrefactor_log_negligible
  fk_length_scaling := T.fkLengthScalingFromMass
  ising_fk_length_agree := T.ising_fk_length_agree


noncomputable def toFKPowerLawTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKPowerLawToIsingAnalyticRGToExponentTarget C :=
  T.toFKMassTarget.toFKPowerLawTarget


end FKMassPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part16


namespace StatMech

namespace Exact3D

namespace FreeMassPowerLawToPlusAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def toFreeMassTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    FreeMassAnalyticRGToPlusExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  freeMass := T.freeMass
  plus_free_agree := T.plus_free_agree
  freeMass_pos := T.freeMass_pos
  freeMass_realizes_inverse_length := T.freeMass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := fun β => (T.massPrefactor β)⁻¹
  prefactor_pos := fun β hβ => inv_pos.mpr (T.massPrefactor_pos β hβ)
  prefactor_log_negligible := by
    refine tendsto_log_inv_prefactor_div_log_betaC_sub Ising3DModel ?_ ?_
    · filter_upwards
        [Ioo_mem_nhdsLT
          (show Ising3DModel.betaC - T.δ < Ising3DModel.betaC by
            rw [Ising3DModel]
            linarith [T.δ_pos])] with β hβ
      exact T.massPrefactor_pos β (by simpa [Ising3DModel] using hβ)
    · simpa [Ising3DModel] using T.massPrefactor_log_negligible
  length_scaling := fun β hβ => T.lengthScalingFromFreeMass hβ


noncomputable def toFreeLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget C :=
  T.toFreeMassTarget.toFreeLengthTarget


noncomputable def toPlusMassTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget C :=
  T.toFreeMassTarget.toPlusMassTarget


noncomputable def toPlusLengthTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toPlusMassTarget.toLengthTarget


def toPlusMassPowerLawTarget
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.freeMass
  mass_pos := T.freeMass_pos
  mass_realizes_inverse_length := fun _ hβ =>
    T.plus_hasInverseCorrelationLength hβ
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  mass_scaling := T.freeMass_scaling

end FreeMassPowerLawToPlusAnalyticRGToExponentTarget
end Exact3D
end StatMech

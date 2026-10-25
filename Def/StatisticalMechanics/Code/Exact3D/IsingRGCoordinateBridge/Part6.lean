/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part7


namespace StatMech

namespace Exact3D

namespace IsingMassRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


def toIsingMassPowerLawTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := T.scaffold.δ
  δ_pos := T.scaffold.δ_pos
  correlationLength := T.scaffold.correlationLength
  mass := T.scaffold.mass
  mass_pos := T.mass_pos
  mass_realizes_inverse_length := T.realizesInverseXAxisLength
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  massPrefactor := T.scaffold.massPrefactor
  massPrefactor_pos := T.massPrefactor_pos
  massPrefactor_log_negligible := T.massPrefactor_log_negligible
  mass_scaling := fun _ hβ => T.mass_scaling hβ


noncomputable def toIsingMassTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingMassAnalyticRGToExponentTarget C :=
  T.toIsingMassPowerLawTarget.toMassTarget


noncomputable def toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toIsingMassTarget.toLengthTarget


end IsingMassRGCoordinateBridgeInputs
end Exact3D
end StatMech

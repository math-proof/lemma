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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part13


namespace StatMech

namespace Exact3D

namespace FreeMassAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


def toFreeLengthTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  plus_free_agree := T.plus_free_agree
  free_realizesXAxisLength := fun _ hβ => T.free_hasCorrelationLength hβ
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling


def toPlusMassTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    IsingMassAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  mass := T.freeMass
  mass_pos := T.freeMass_pos
  mass_realizes_inverse_length := fun _ hβ =>
    T.plus_hasInverseCorrelationLength hβ
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling


def toPlusLengthTarget
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    IsingAnalyticRGToExponentTarget C :=
  T.toPlusMassTarget.toLengthTarget

end FreeMassAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech

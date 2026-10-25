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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part10


namespace StatMech

namespace Exact3D

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


def toPlusLengthTarget
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    IsingAnalyticRGToExponentTarget C where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  realizesXAxisLength := fun _ hβ => T.plus_hasCorrelationLength hβ
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := T.length_scaling

end FreeAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech

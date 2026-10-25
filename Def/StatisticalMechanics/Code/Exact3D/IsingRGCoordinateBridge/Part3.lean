/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part3


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


def toIsingAnalyticTarget
    (T : IsingRGCoordinateBridgeInputs C) :
    IsingAnalyticRGToExponentTarget C where
  δ := T.scaffold.δ
  δ_pos := T.scaffold.δ_pos
  correlationLength := T.scaffold.correlationLength
  realizesXAxisLength := T.realizesXAxisLength
  prefactor := T.scaffold.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := fun _ hβ => T.length_scaling hβ


end IsingRGCoordinateBridgeInputs
end Exact3D
end StatMech

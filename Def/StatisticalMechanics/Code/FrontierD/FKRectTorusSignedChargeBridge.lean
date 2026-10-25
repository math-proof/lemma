/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

def fkRectOrientedLoopWeight (R : FKRectTorus) (lam : Real)
    (omega : R.Configuration) (arrows : SixVertexArrows R.medialTorus) : Real :=
  fkOrientedLoopPairingWeight lam
    (fkRectConfigurationToMedialPairing R omega) arrows


def fkRectOrientedLoopPartitionSum (R : FKRectTorus) (lam : Real) : Real :=
  ∑ omega : R.Configuration,
    ∑ arrows : SixVertexArrows R.medialTorus,
      fkRectOrientedLoopWeight R lam omega arrows

end
end StatMech.FrontierD

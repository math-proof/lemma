/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge.Part2
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

def fkRectSignedChargeTilt (R : FKRectTorus) (q lam : Real)
    (n : Fin (R.medialTorus.width + 1))
    (omega : R.Configuration) : Real :=
  (∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) /
    fkRectCriticalReducedWeight R q omega


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

def fkRectOrientedLoopSectorPartitionSum
    (R : FKRectTorus) (n : Fin (R.medialTorus.width + 1))
    (lam : Real) : Real :=
  ∑ omega : R.Configuration,
    ∑ arrows : SixVertexArrows R.medialTorus,
      if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) = n.val then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0

end
end StatMech.FrontierD

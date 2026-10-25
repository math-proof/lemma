/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalReducedWeight (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  Real.sqrt q ^ fkRectOpenEdgeCount R omega *
    q ^ fkRectNumClusters R omega


end
end StatMech.FrontierD

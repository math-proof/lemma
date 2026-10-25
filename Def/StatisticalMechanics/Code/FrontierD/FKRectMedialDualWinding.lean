/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialDualWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5


namespace StatMech.FrontierD

noncomputable section

def fkRectMedialDualShiftColumnEquiv (R : FKRectTorus) :
    Fin R.medialTorus.width ≃ Fin R.medialTorus.width where
  toFun := SixVertexArrows.cyclicPred R.medialTorus.width_pos
  invFun := finitePeriodicSucc R.medialTorus.width_pos
  left_inv := finitePeriodicSucc_cyclicPred R.medialTorus.width_pos
  right_inv := svCyclicPred_finitePeriodicSucc R.medialTorus.width_pos

end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedSectorNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectCriticalReducedAreaDensity
    (R : FKRectTorus) (q : Real) : Real :=
  Real.log (fkRectCriticalReducedZ R q) /
    (R.width * R.height : Nat)


noncomputable def fkRectBalancedSectorAreaDensity
    (R : FKRectTorus) (q : Real) : Real :=
  Real.log
      (sixVertexTorusFixedChargePartitionSum R.medialTorus 0
        (Nat.zero_le _) (fkQgt4SixVertexWeight q)) /
    (R.width * R.height : Nat)


noncomputable def fkRectBalancedNormalizationDefectDensity
    (R : FKRectTorus) (q : Real) : Real :=
  -Real.log (fkRectBalancedSectorNormalization R q) /
    (R.width * R.height : Nat)


end
end StatMech.FrontierD

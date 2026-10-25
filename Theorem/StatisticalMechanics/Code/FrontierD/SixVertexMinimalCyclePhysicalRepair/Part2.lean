/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem SixVertexDisjointCapUnitRepair.toUnitCycleRepair_target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    repair.toUnitCycleRepair.target = repair.target := rfl


end
end StatMech.FrontierD

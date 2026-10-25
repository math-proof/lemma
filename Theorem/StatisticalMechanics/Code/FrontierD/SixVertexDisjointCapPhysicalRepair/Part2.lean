/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDisjointCapPhysicalTarget_arrows
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (repair : SixVertexDisjointCapUnitRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade) :
    ((sixVertexDisjointCapPhysicalTarget source repair).1.1,
        (sixVertexDisjointCapPhysicalTarget source repair).2.1) =
      repair.target := by
  rfl


end
end StatMech.FrontierD

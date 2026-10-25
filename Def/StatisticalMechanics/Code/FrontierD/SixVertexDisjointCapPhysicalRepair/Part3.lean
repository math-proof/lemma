/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalArrowPairGrade
    {T : EvenTorus} (pair : SixVertexArrows T × SixVertexArrows T) :
    Nat × Nat :=
  (sixVertexTorusCTypeCount pair.1 + sixVertexTorusCTypeCount pair.2, 0)


def sixVertexDisjointCapPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (repair : SixVertexDisjointCapUnitRepair source.1.1 source.2.1
      sixVertexPhysicalArrowPairGrade) :
    SixVertexConfigurationPhysicalTarget T middle := by
  have hice := repair.target_ice source.1.2.1 source.2.2.1
  have hfirstInt :
      (sixVertexUpCount
          (svTorusVerticalRows T repair.target.1
            (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [repair.first_upCount, source.1.2.2]
    push_cast
    omega
  have hsecondInt :
      (sixVertexUpCount
          (svTorusVerticalRows T repair.target.2
            (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [repair.second_upCount, source.2.2.2]
    push_cast
    omega
  exact (⟨repair.target.1, hice.1, by exact_mod_cast hfirstInt⟩,
    ⟨repair.target.2, hice.2, by exact_mod_cast hsecondInt⟩)

end
end StatMech.FrontierD

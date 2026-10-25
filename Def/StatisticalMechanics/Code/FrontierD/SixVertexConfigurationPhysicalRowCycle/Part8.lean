/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexPhysicalRowCyclePairedBranchEmbeddings.toPhysical
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (rowEmbeddings : SixVertexPhysicalRowCyclePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt where
  branch choice :=
    sixVertexPhysicalSourceEquivRowCycles.toEmbedding |>.trans
      (rowEmbeddings.branch choice) |>.trans
      sixVertexPhysicalTargetEquivRowCycles.symm.toEmbedding
  distinct source := by
    intro heq
    apply rowEmbeddings.distinct (sixVertexPhysicalSourceEquivRowCycles source)
    apply sixVertexPhysicalTargetEquivRowCycles.symm.injective
    exact heq
  aggregateTotalC source := by
    have h := rowEmbeddings.aggregateTotalC
      (sixVertexPhysicalSourceEquivRowCycles
        (hmiddle_pos := hmiddle_pos) (hmiddle_lt := hmiddle_lt) source)
    rw [sixVertexPhysicalSourceEquivRowCycles_totalC] at h
    simpa using h


end
end StatMech.FrontierD

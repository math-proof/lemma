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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexPhysicalRowCycleExactGradeCapacity
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall totalC,
    Nonempty
      ({source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt //
        sixVertexPhysicalRowCyclePairTotalC source = totalC} ↪
      {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
        sixVertexPhysicalRowCyclePairTotalC target.1 = totalC})

set_option maxHeartbeats 1000000 in

noncomputable def
    sixVertexPhysicalRowCyclePairedBranchEmbeddings_of_exactGradeCapacity
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (hcapacity : SixVertexPhysicalRowCycleExactGradeCapacity
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexPhysicalRowCyclePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt := by
  classical
  let fiberEmbedding : forall totalC,
      {source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt //
        sixVertexPhysicalRowCyclePairTotalC source = totalC} ↪
      {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
        sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} :=
    fun totalC => Classical.choice (hcapacity totalC)
  let gradedEmbedding :
      (Sigma fun totalC =>
        {source : SixVertexPhysicalRowCycleSource T middle
            hmiddle_pos hmiddle_lt //
          sixVertexPhysicalRowCyclePairTotalC source = totalC}) ↪
      (Sigma fun totalC =>
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC}) :=
    { toFun := fun graded =>
        ⟨graded.1, fiberEmbedding graded.1 graded.2⟩
      inj' := by
        rintro ⟨firstTotal, first⟩ ⟨secondTotal, second⟩ heq
        have htotal : firstTotal = secondTotal := congrArg Sigma.fst heq
        subst secondTotal
        have hfiber : fiberEmbedding firstTotal first =
            fiberEmbedding firstTotal second := by
          exact eq_of_heq (Sigma.mk.inj heq).2
        have hsource := (fiberEmbedding firstTotal).injective hfiber
        cases hsource
        rfl }
  let matchingEmbedding :
      SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt ↪
        SixVertexPhysicalRowCycleOffDiagonalTarget T middle :=
    (Equiv.sigmaFiberEquiv
      (fun source : SixVertexPhysicalRowCycleSource T middle
          hmiddle_pos hmiddle_lt =>
        sixVertexPhysicalRowCyclePairTotalC source)).symm.toEmbedding |>.trans
      (gradedEmbedding.trans
        (Equiv.sigmaFiberEquiv
          (fun target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle =>
            sixVertexPhysicalRowCyclePairTotalC target.1)).toEmbedding)
  exact
    { branch := fun choice =>
        matchingEmbedding.trans
          (if choice then sixVertexPhysicalRowCycleOffDiagonalSwap
            else sixVertexPhysicalRowCycleOffDiagonalForget)
      distinct := by
        intro source
        simpa [matchingEmbedding] using
          sixVertexPhysicalRowCycleOffDiagonal_branches_distinct
            (matchingEmbedding source)
      aggregateTotalC := by
        intro source
        have hs : sixVertexPhysicalRowCyclePairTotalC
              (matchingEmbedding source).1 =
            sixVertexPhysicalRowCyclePairTotalC source := by
          simpa [matchingEmbedding, gradedEmbedding] using
            (fiberEmbedding
              (sixVertexPhysicalRowCyclePairTotalC source)
              ⟨source, rfl⟩).2
        simp only [matchingEmbedding, Function.Embedding.trans_apply,
          Bool.false_eq_true, if_false, if_true]
        rw [sixVertexPhysicalRowCycleOffDiagonalSwap_totalC]
        change 2 * sixVertexPhysicalRowCyclePairTotalC source <=
          sixVertexPhysicalRowCyclePairTotalC (matchingEmbedding source).1 +
            sixVertexPhysicalRowCyclePairTotalC (matchingEmbedding source).1
        omega }

end
end StatMech.FrontierD

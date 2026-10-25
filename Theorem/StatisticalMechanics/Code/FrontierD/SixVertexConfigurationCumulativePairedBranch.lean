/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationCumulativePairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationCumulativePairedBranch.Part2


namespace StatMech.FrontierD

noncomputable section

theorem SixVertexConfigurationCumulativePairedBranchEmbeddings.upperCumulative
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    ∀ totalC,
      (Finset.univ.filter fun pair :
          SixVertexConfigurationCumulativeSource T middle hmiddle_pos
            hmiddle_lt =>
        totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card ≤
      (Finset.univ.filter fun pair :
          SixVertexConfigurationCumulativeTarget T middle =>
        totalC ≤ sixVertexConfigurationCumulativeTotalC pair).card :=
  TwoBranchMonotoneEmbeddings.upperCumulative embeddings


theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_cumulativePairedBranches
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (embeddings : SixVertexConfigurationCumulativePairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  apply sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCCumulative
    T middle hmiddle_pos hmiddle_lt
  intro totalC
  simpa [sixVertexConfigurationCumulativeTotalC] using
    embeddings.upperCumulative totalC

end
end StatMech.FrontierD

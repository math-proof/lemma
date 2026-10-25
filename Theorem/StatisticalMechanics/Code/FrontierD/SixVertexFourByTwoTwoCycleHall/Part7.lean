/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoConfigurationPairMatching_injective :
    Function.Injective sixVertexFourByTwoConfigurationPairMatching := by
  intro source₁ source₂ heq
  apply sixVertexFourByTwoSourcePairEquiv.symm.injective
  apply sixVertexFourByTwoMatchingIndex_injective
  apply sixVertexFourByTwoTargetPairEquiv.injective
  exact heq

theorem sixVertexFourByTwoConfigurationPairMatching_fineRelated
    (source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorZero ×
      SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
        sixVertexFourByTwoSectorTwo) :
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((sixVertexFourByTwoConfigurationPairMatching source).1.1,
        (sixVertexFourByTwoConfigurationPairMatching source).2.1) := by
  let i := sixVertexFourByTwoSourcePairEquiv.symm source
  have hsource := sixVertexFourByTwoSourcePairEquiv.apply_symm_apply source
  change sixVertexPairAtMostTwoCycleFineRelated
    (source.1.1, source.2.1)
    ((sixVertexFourByTwoTargetPairEquiv
      (sixVertexFourByTwoMatchingIndex i)).1.1,
      (sixVertexFourByTwoTargetPairEquiv
      (sixVertexFourByTwoMatchingIndex i)).2.1)
  rw [← hsource]
  exact sixVertexFourByTwoMatchingIndex_fineRelated i


theorem sixVertexFourByTwo_configurationPairTwoCycleFineHall :
    SixVertexConfigurationPairTwoCycleFineHall sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorTwo := by
  rw [configurationPairTwoCycleFineHall_iff_exists_injective]
  exact ⟨sixVertexFourByTwoConfigurationPairMatching,
    sixVertexFourByTwoConfigurationPairMatching_injective,
    sixVertexFourByTwoConfigurationPairMatching_fineRelated⟩

theorem sixVertexFourByTwo_markedTraceCoefficientwiseLogConcave :
    SixVertexMarkedTraceCoefficientwiseLogConcave 4 2 1 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne])
      sixVertexFourByTwo_configurationPairTwoCycleFineHall

theorem sixVertexFourByTwo_sectorTrace_logConcave
    {c : Real} (hc : 2 <= c) :
    Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) *
        Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <=
      Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
  simpa [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne] using
    sixVertexSectorTrace_logConcave_of_twoCycleFineHall
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      (by norm_num [sixVertexFourByTwoSectorOne])
      (by norm_num [sixVertexFourByTwoTorus, sixVertexFourByTwoSectorOne])
      hc sixVertexFourByTwo_configurationPairTwoCycleFineHall

end
end StatMech.FrontierD

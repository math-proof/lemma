/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexConfigurationPhysicalPairedBranchEmbeddings.particleHole
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embeddings : SixVertexConfigurationPhysicalPairedBranchEmbeddings
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T
      (sixVertexPhysicalParticleHoleMiddle middle)
      (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
      (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos) where
  branch choice :=
    (sixVertexPhysicalParticleHoleSourceEmbedding
      (middle := middle)).trans
      ((embeddings.branch choice).trans
        (sixVertexPhysicalParticleHoleTargetEmbedding
          (middle := middle)))
  distinct source := by
    intro heq
    apply embeddings.distinct
      (sixVertexPhysicalParticleHoleSourceEmbedding source)
    apply sixVertexPhysicalParticleHoleTargetEmbedding.injective
    exact heq
  aggregateTotalC source := by
    change
      2 * sixVertexConfigurationPairTotalCPhysical source <=
        sixVertexConfigurationPairTotalCPhysical
            (sixVertexPhysicalParticleHoleTargetEmbedding
              (embeddings.branch false
                (sixVertexPhysicalParticleHoleSourceEmbedding source))) +
          sixVertexConfigurationPairTotalCPhysical
            (sixVertexPhysicalParticleHoleTargetEmbedding
              (embeddings.branch true
                (sixVertexPhysicalParticleHoleSourceEmbedding source)))
    simp only [sixVertexPhysicalParticleHoleTargetEmbedding_totalC]
    rw [← sixVertexPhysicalParticleHoleSourceEmbedding_totalC source]
    exact embeddings.aggregateTotalC
      (sixVertexPhysicalParticleHoleSourceEmbedding source)

end
end StatMech.FrontierD

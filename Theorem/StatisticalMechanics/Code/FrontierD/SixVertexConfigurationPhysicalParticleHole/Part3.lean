/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexPhysicalParticleHoleSourceEmbedding_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T
      (sixVertexPhysicalParticleHoleMiddle middle)
      (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
      (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos)) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalParticleHoleSourceEmbedding
          (middle := middle) (hmiddle_pos := hmiddle_pos)
          (hmiddle_lt := hmiddle_lt) source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  simp [sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalParticleHoleSourceEmbedding, Nat.add_comm]

@[simp] theorem sixVertexPhysicalParticleHoleTargetEmbedding_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalParticleHoleTargetEmbedding target) =
      sixVertexConfigurationPairTotalCPhysical target := by
  simp [sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalParticleHoleTargetEmbedding]


end
end StatMech.FrontierD

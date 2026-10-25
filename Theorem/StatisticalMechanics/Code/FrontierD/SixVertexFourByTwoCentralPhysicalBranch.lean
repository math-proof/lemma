/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoSectorThreeConfiguration_injective :
    Function.Injective sixVertexFourByTwoSectorThreeConfiguration := by
  intro first second heq
  apply sixVertexFourByTwoSectorOneConfiguration_injective
  apply Subtype.ext
  apply sixVertexArrowsComplement_injective
  exact congrArg Subtype.val heq

theorem sixVertexFourByTwoSectorThreeConfiguration_surjective :
    Function.Surjective sixVertexFourByTwoSectorThreeConfiguration := by
  intro eta
  let hole : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
    ⟨sixVertexArrowsComplement eta.1,
      sixVertexArrowsComplement_iceRule eta.2.1, by
        change sixVertexUpCount (fun x =>
          !eta.1.vertical
            (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 1
        rw [sixVertexUpCount_complement]
        have hsector := eta.2.2
        change sixVertexUpCount (fun x =>
          eta.1.vertical
            (x, svFinLast sixVertexFourByTwoTorus.height_pos)) = 3 at hsector
        rw [hsector]
        norm_num [sixVertexFourByTwoTorus]⟩
  obtain ⟨i, hi⟩ := sixVertexFourByTwoSectorOneConfiguration_surjective hole
  refine ⟨i, Subtype.ext ?_⟩
  have harrows := congrArg Subtype.val hi
  change (sixVertexFourByTwoSectorOneConfiguration i).1 =
    sixVertexArrowsComplement eta.1 at harrows
  have hcomplement := congrArg sixVertexArrowsComplement harrows
  simpa [sixVertexFourByTwoSectorThreeConfiguration] using hcomplement

end
end StatMech.FrontierD

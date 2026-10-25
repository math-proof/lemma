/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalChooseSum_eq_profileAggregate
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :
    (∑ horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade},
      sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 *
        sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) =
      ∑ profile : SixVertexHorizontalPairCompletionProfile T,
        sixVertexHorizontalPairProfileMultiplicity T grade profile *
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
  simp_rw [sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [<- Finset.sum_fiberwise Finset.univ
    (fun horizontal :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} =>
      sixVertexHorizontalPairCompletionProfile T horizontal.1)
    (fun horizontal =>
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal.1))]
  apply Finset.sum_congr rfl
  intro profile hprofile
  rw [sixVertexHorizontalPairProfileMultiplicity, Fintype.card_subtype]
  let fiber := (Finset.univ.filter fun horizontal :
      {horizontal : SixVertexHorizontalField T ×
          SixVertexHorizontalField T //
        sixVertexHorizontalPairBigrade horizontal = grade} =>
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile)
  change (∑ horizontal ∈ fiber,
      sixVertexHorizontalPairProfileChooseWeight left right
        (sixVertexHorizontalPairCompletionProfile T horizontal.1)) =
    fiber.card * sixVertexHorizontalPairProfileChooseWeight left right profile
  calc
    _ = ∑ _horizontal ∈ fiber,
          sixVertexHorizontalPairProfileChooseWeight left right profile := by
      apply Finset.sum_congr rfl
      intro horizontal hhorizontal
      have hprofileEq :
          sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile :=
        (Finset.mem_filter.mp hhorizontal).2
      rw [hprofileEq]
    _ = _ := by simp


end
end StatMech.FrontierD

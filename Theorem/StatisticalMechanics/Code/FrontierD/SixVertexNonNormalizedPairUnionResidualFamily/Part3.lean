/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexNonNormalizedPairUnionResidualFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexNonNormalizedPairUnionResidualFamily.Part2


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexNonNormalizedPairUnionPhysicalTargetFamily

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}


theorem decode_surplusTarget
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    family.decoder (family.surplusTarget (source, branch)) =
      some source.1.1 := by
  let coded := (source, branch)
  have hexists : ∃ candidate,
      family.surplusEmbedding candidate = family.surplusTarget coded :=
    ⟨coded, rfl⟩
  rw [decoder, dif_pos hexists]
  have hchosen : Classical.choose hexists = coded := by
    apply family.surplusEmbedding.injective
    exact Classical.choose_spec hexists
  rw [hchosen]


theorem surplusTarget_supported
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (source : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt grade source.1.1
        (family.surplusTarget (source, branch)) := by
  change SixVertexConfigurationPairTwoCycleFineRelated
    (sixVertexHorizontalActualDeficitConfigurationPair source.1.1).1
    (sixVertexHorizontalActualSurplusConfigurationPair
      (family.surplusTarget (source, branch))).1
  rw [family.surplusTarget_physical]
  exact family.related source branch


theorem surplusTarget_joint_injective
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade) :
    Function.Injective (fun coded => family.surplusTarget coded) :=
  family.surplusEmbedding.injective


theorem surplusTarget_branch_injective
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (branch : Bool) :
    Function.Injective (fun source => family.surplusTarget (source, branch)) := by
  intro first second heq
  exact congrArg Prod.fst (family.surplusEmbedding.injective heq)


theorem surplusTarget_branches_disjoint
    (family : SixVertexNonNormalizedPairUnionPhysicalTargetFamily T middle
      hmiddle_pos hmiddle_lt grade)
    (first second : SixVertexNonNormalizedUnitChargeResidualSources T middle
      hmiddle_pos hmiddle_lt grade) :
    family.surplusTarget (first, false) ≠
      family.surplusTarget (second, true) := by
  intro heq
  have hcoded : (first, false) = (second, true) :=
    family.surplusEmbedding.injective heq
  exact Bool.false_ne_true (congrArg Prod.snd hcoded)


end SixVertexNonNormalizedPairUnionPhysicalTargetFamily
end
end StatMech.FrontierD

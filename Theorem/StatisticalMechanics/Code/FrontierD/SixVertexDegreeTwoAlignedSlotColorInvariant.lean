/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle ↔
      x.1 ∈ sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle := by
  rcases x with ⟨dart, branch⟩
  cases branch <;>
    simp [sixVertexDegreeTwoBranchClosedUnitPrefix]

theorem sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap x ∈
        sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle ↔
      x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle := by
  rw [mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff,
    mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff]
  rfl

theorem sixVertexDegreeTwoBranchClosedUnitPrefix_charge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
        (doubledAlignedCharge hdegree)).sum = 1 := by
  rw [sixVertexDegreeTwoBranchClosedUnitPrefix]
  simp only [List.map_flatMap]
  change (((sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
    homegaSector hetaSector hmiddle).flatMap fun dart =>
      [sixVertexDegreeTwoStrandStepSeamSign hdegree dart, 0]).sum) = 1
  have hcollapse (darts :
      List (SixVertexOrientedDisagreementDart omega eta)) :
      (darts.flatMap fun dart =>
          [sixVertexDegreeTwoStrandStepSeamSign hdegree dart, 0]).sum =
        (darts.map
          (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum := by
    induction darts with
    | nil => rfl
    | cons dart darts ih => simp [ih]
  rw [hcollapse]
  exact sixVertexDegreeTwoCanonicalUnitPrefix_sum
    homega heta hdegree middle homegaSector hetaSector hmiddle


end
end StatMech.FrontierD

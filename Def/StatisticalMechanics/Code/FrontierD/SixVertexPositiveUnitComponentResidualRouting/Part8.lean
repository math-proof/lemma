/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Inductive.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part2


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexHorizontalResidualGeometricCertificate

variable {T : EvenTorus} {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle
    hmiddle_pos hmiddle_lt grade}


noncomputable def ofUnitStrand
    (hdegree : SixVertexLocallyDegreeTwo
      source.1.1.1.1 source.1.1.2.1)
    (seed : SixVertexOrientedDisagreementDart
      source.1.1.1.1 source.1.1.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord
      source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed).sum = 1) :
    SixVertexHorizontalResidualGeometricCertificate source := by
  let mask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed).mask
  have hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true →
      sixVertexTorusEdgeDisagrees source.1.1.1.1 source.1.1.2.1 edge :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees
      source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed
  have hbalanced : SixVertexBalancedFlipMask source.1.1.1.1 mask :=
    sixVertexBalancedFlipMask_of_ice_flip source.1.1.1.2.1
      (sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
        source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed)
  have hfull : SixVertexFullDisagreementMask
      source.1.1.1.1 source.1.1.2.1 mask :=
    hbalanced.fullDisagreementMask_of_degreeTwo hdegree hsupport
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      source.1.1.1.1 source.1.1.2.1 = 1 := by
    calc
      sixVertexTorusMaskSeamTransfer mask source.1.1.1.1 source.1.1.2.1 =
          sixVertexTorusFlipSeamDelta mask source.1.1.1.1 :=
        sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees hsupport
      _ = (sixVertexDegreeTwoStrandSeamWord source.1.1.1.2.1
          source.1.1.2.2.1 hdegree seed).sum :=
        sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum
          source.1.1.1.2.1 source.1.1.2.2.1 hdegree seed
      _ = 1 := hunit
  refine SixVertexHorizontalResidualGeometricCertificate.fullMask ?_
  refine ⟨mask, ?_, ?_⟩
  · simpa only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows] using hfull
  · simpa only [sixVertexLoopDecoratedPairColored_false_arrows,
      sixVertexLoopDecoratedPairColored_true_arrows] using htransfer


noncomputable def loopTarget
    (certificate : SixVertexHorizontalResidualGeometricCertificate source) :
    SixVertexHorizontalDegreeTwoLoopHallTarget T middle grade :=
  match certificate with
  | .fullMask full =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source
        (sixVertexHorizontalDegreeTwoLoopFullUnitMaskSpliceKey source full)
  | .resolvedCross cross =>
      sixVertexHorizontalDegreeTwoLoopSpliceTarget source
        (sixVertexHorizontalDegreeTwoLoopResolvedUnitCrossSpliceKey source cross)
  | .fineRelated target _ => target


end SixVertexHorizontalResidualGeometricCertificate
end
end StatMech.FrontierD

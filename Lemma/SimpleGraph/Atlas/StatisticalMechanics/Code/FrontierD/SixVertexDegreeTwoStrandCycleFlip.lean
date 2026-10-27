import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFlip
open StatMech StatMech.FrontierD


/--
[sixVertexDirectedTorusEdgeOfArrow_follows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_follows_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {edge : SixVertexTorusEdge T} :
-- imply
  (sixVertexDirectedTorusEdgeOfArrow omega edge).Follows omega := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_follows omega edge

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_follows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_follows_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).Follows omega := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_follows homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandCycleEnumeration_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandCycleEnumeration_eq_pow_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {i : Fin (orderOf (sixVertexDegreeTwoStrandCyclePerm homega heta hdegree seed))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i = ((sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree) ^ i.val) seed := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandCycleEnumeration_eq_pow homega heta hdegree seed i

/--
[sixVertexDirectedTorusEdgeOfArrow_seamFlow_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdgeOfArrow_seamFlow_of_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {edge : SixVertexTorusEdge T}
-- given
  (hdisagrees : sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  (∑ column : Fin T.width, (sixVertexDirectedTorusEdgeOfArrow omega edge).verticalFlow (column, svFinLast T.height_pos)) = -sixVertexTorusEdgeSeamSign omega eta edge := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdgeOfArrow_seamFlow_of_disagrees edge hdisagrees

/--
[sixVertexDegreeTwoOrientedStrandEdge_seamFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedStrandEdge_seamFlow_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∑ column : Fin T.width, (sixVertexDegreeTwoOrientedStrandEdge hdegree dart).verticalFlow (column, svFinLast T.height_pos)) = -sixVertexDegreeTwoStrandStepSeamSign hdegree dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedStrandEdge_seamFlow hdegree dart

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_seamFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_seamFlow_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∑ column : Fin T.width, (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).verticalFlow (column, svFinLast T.height_pos)) = -∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_seamFlow homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandSeamWord_sum_eq_cycleEnumeration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandSeamWord_sum_eq_cycleEnumeration_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed).sum = ∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandSeamWord_sum_eq_cycleEnumeration homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexTorusFlipSeamDelta (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask omega = ∑ i, sixVertexDegreeTwoStrandStepSeamSign hdegree (sixVertexDegreeTwoStrandCycleEnumeration homega heta hdegree seed i) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexTorusFlipSeamDelta (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask omega = (sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed).sum := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexTorusFlip (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask omega).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {edge : SixVertexTorusEdge T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hselected : sixVertexTorusMaskSelects (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask edge = true) :
-- imply
  sixVertexTorusEdgeDisagrees omega eta edge := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_disagrees homega heta hdegree seed edge hselected

/--
[sixVertexLocalBalancedFlipMask_transfer_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexLocalBalancedFlipMask_transfer_of_disagrees_eq
  {first second mask : SixVertexLocalIncomingPattern}
-- given
  (hbalanced : SixVertexLocalBalancedFlipMask first mask)
  (hdisagrees : ∀ side, mask side = true → first side ≠ second side) :
-- imply
  SixVertexLocalBalancedFlipMask second mask := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalBalancedFlipMask_transfer_of_disagrees first second mask hbalanced hdisagrees

/--
[SixVertexBalancedFlipMask.transfer_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma transfer_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hbalanced : SixVertexBalancedFlipMask omega mask)
  (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  SixVertexBalancedFlipMask eta mask := by
-- proof
  apply StatMech.FrontierD.SixVertexBalancedFlipMask.transfer_of_disagrees hbalanced hdisagrees

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_balanced_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_balanced_second_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  SixVertexBalancedFlipMask eta (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_mask_balanced_second homega heta hdegree seed

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexTorusFlip (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask eta).IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice homega heta hdegree seed

/--
[sixVertexTorusFlipSeamDelta_eq_neg_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexTorusFlipSeamDelta_eq_neg_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexTorusFlipSeamDelta mask eta = -sixVertexTorusFlipSeamDelta mask omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFlipSeamDelta_eq_neg_of_disagrees hdisagrees

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexTorusFlipSeamDelta (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask eta = -(sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed).sum := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta homega heta hdegree seed

/--
[sixVertexPairUnionHorizontal_bothFlip_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexPairUnionHorizontal_bothFlip_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexPairUnionHorizontal (sixVertexTorusFlip mask omega, sixVertexTorusFlip mask eta) = sixVertexPairUnionHorizontal (omega, eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnionHorizontal_bothFlip_of_disagrees hdisagrees

/--
[sixVertexPairUnionVertical_bothFlip_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexPairUnionVertical_bothFlip_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hdisagrees : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexPairUnionVertical (sixVertexTorusFlip mask omega, sixVertexTorusFlip mask eta) = sixVertexPairUnionVertical (omega, eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnionVertical_bothFlip_of_disagrees hdisagrees

/--
[sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_pair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleFlip.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_pair_related_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexPairAtMostTwoCycleRelated (omega, eta) (sixVertexTorusFlip (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask omega, eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_pair_related homega heta hdegree seed


-- created on 2026-10-23

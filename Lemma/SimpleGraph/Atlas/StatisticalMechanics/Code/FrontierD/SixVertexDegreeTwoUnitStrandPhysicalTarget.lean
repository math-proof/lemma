import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalTarget
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) = (sixVertexTorusFlip (sixVertexDegreeTwoStrandDirectedSimpleCycle source.1.2.1 source.2.2.1 hdegree seed).mask source.1.1, sixVertexTorusFlip (sixVertexDegreeTwoStrandDirectedSimpleCycle source.1.2.1 source.2.2.1 hdegree seed).mask source.2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_arrows source hdegree seed hunit

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_horizontalUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_horizontalUnion_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  sixVertexPairUnionHorizontal ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) = sixVertexPairUnionHorizontal (source.1.1, source.2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_horizontalUnion source hdegree seed hunit

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_verticalUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_verticalUnion_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  sixVertexPairUnionVertical ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) = sixVertexPairUnionVertical (source.1.1, source.2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_verticalUnion source hdegree seed hunit

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_pair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_pair_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  sixVertexPairAtMostTwoCycleRelated (source.1.1, source.2.1) ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_pair_related source hdegree seed hunit

/--
[sixVertexLocalBalancedFlipMask_full_of_degreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexLocalBalancedFlipMask_full_of_degreeTwo_eq
  {first second mask : SixVertexLocalIncomingPattern}
-- given
  (hdegree : (sixVertexLocalDisagreementSides first second).card = 0 ∨ (sixVertexLocalDisagreementSides first second).card = 2)
  (hbalanced : SixVertexLocalBalancedFlipMask first mask)
  (hsupport : ∀ side, mask side = true → first side ≠ second side) :
-- imply
  ∀ selected other, mask selected = true → first other ≠ second other → mask other = true := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalBalancedFlipMask_full_of_degreeTwo first second mask hdegree hbalanced hsupport

/--
[SixVertexBalancedFlipMask.fullDisagreementMask_of_degreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma fullDisagreementMask_of_degreeTwo_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hbalanced : SixVertexBalancedFlipMask omega mask)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  SixVertexFullDisagreementMask omega eta mask := by
-- proof
  apply StatMech.FrontierD.SixVertexBalancedFlipMask.fullDisagreementMask_of_degreeTwo hbalanced hdegree hsupport

/--
[sixVertexTorusSwitchFirst_eq_flip_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexTorusSwitchFirst_eq_flip_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexTorusSwitchFirst mask omega eta = sixVertexTorusFlip mask omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchFirst_eq_flip_of_disagrees hsupport

/--
[sixVertexTorusSwitchSecond_eq_flip_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexTorusSwitchSecond_eq_flip_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexTorusSwitchSecond mask omega eta = sixVertexTorusFlip mask eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchSecond_eq_flip_of_disagrees hsupport

/--
[sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hsupport : ∀ edge, sixVertexTorusMaskSelects mask edge = true → sixVertexTorusEdgeDisagrees omega eta edge) :
-- imply
  sixVertexTorusMaskSeamTransfer mask omega eta = sixVertexTorusFlipSeamDelta mask omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMaskSeamTransfer_eq_flipSeamDelta_of_disagrees hsupport

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_fine_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (source.1.1.horizontal, source.2.1.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1.horizontal, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_fine source hdegree seed hunit

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (source.1.1, source.2.1) ((sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1.1, (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_fineRelated source hdegree seed hunit

/--
[sixVertexTorusBothFlip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexTorusBothFlip_injective_eq
  {T : EvenTorus}
  {mask : SixVertexArrows T} :
-- imply
  Function.Injective (fun pair : SixVertexArrows T × SixVertexArrows T => (sixVertexTorusFlip mask pair.1, sixVertexTorusFlip mask pair.2)) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusBothFlip_injective mask

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_recover_of_mask_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_recover_of_mask_eq_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {first second : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seedFirst : SixVertexOrientedDisagreementDart first.1.1 first.2.1}
  {seedSecond : SixVertexOrientedDisagreementDart second.1.1 second.2.1}
-- given
  (hdegreeFirst : SixVertexLocallyDegreeTwo first.1.1 first.2.1)
  (hdegreeSecond : SixVertexLocallyDegreeTwo second.1.1 second.2.1)
  (hunitFirst : (sixVertexDegreeTwoStrandSeamWord first.1.2.1 first.2.2.1 hdegreeFirst seedFirst).sum = 1)
  (hunitSecond : (sixVertexDegreeTwoStrandSeamWord second.1.2.1 second.2.2.1 hdegreeSecond seedSecond).sum = 1)
  (hmask : (sixVertexDegreeTwoStrandDirectedSimpleCycle first.1.2.1 first.2.2.1 hdegreeFirst seedFirst).mask = (sixVertexDegreeTwoStrandDirectedSimpleCycle second.1.2.1 second.2.2.1 hdegreeSecond seedSecond).mask)
  (htarget : sixVertexDegreeTwoUnitStrandPhysicalTarget first hdegreeFirst seedFirst hunitFirst = sixVertexDegreeTwoUnitStrandPhysicalTarget second hdegreeSecond seedSecond hunitSecond) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_recover_of_mask_eq first second hdegreeFirst hdegreeSecond seedFirst seedSecond hunitFirst hunitSecond hmask htarget

/--
[sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean)
-/
@[path]
private lemma sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
  (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1 source.2.2.1 hdegree seed).sum = 1) :
-- imply
  (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).1 ≠ (sixVertexDegreeTwoUnitStrandPhysicalTarget source hdegree seed hunit).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoUnitStrandPhysicalTarget_layers_ne source hdegree seed hunit


-- created on 2026-10-23

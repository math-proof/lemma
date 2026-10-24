import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation
open StatMech StatMech.FrontierD


/--
[sixVertexLoopDecoratedPairColored_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_injective_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)} :
-- imply
  Function.Injective (sixVertexLoopDecoratedPairColored : SixVertexLoopDecoratedPair T left right -> FKColoredLoopPairingPair T) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_injective

/--
[fkColoredFullSwapTarget_injective_fixedMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_injective_fixedMask_eq
  {T : EvenTorus}
  {first second : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hfirst : FKColoredFullSwapBondCoherent first mask)
  (hsecond : FKColoredFullSwapBondCoherent second mask)
  (heq : fkColoredFullSwapTarget first mask hfirst = fkColoredFullSwapTarget second mask hsecond) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_injective_fixedMask mask first second hfirst hsecond heq

/--
[fkColoredFullSwapTarget_injective_of_mask_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_injective_of_mask_eq_eq
  {T : EvenTorus}
  {first second : FKColoredLoopPairingPair T}
-- given
  (firstMask secondMask : T.Vertex -> Bool)
  (hfirst : FKColoredFullSwapBondCoherent first firstMask)
  (hsecond : FKColoredFullSwapBondCoherent second secondMask)
  (hmasks : firstMask = secondMask)
  (heq : fkColoredFullSwapTarget first firstMask hfirst = fkColoredFullSwapTarget second secondMask hsecond) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_injective_of_mask_eq firstMask secondMask first second hfirst hsecond hmasks heq

/--
[sixVertexTorusMaskSeamTransfer_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexTorusMaskSeamTransfer_pairSwitch_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusMaskSeamTransfer mask (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) = -sixVertexTorusMaskSeamTransfer mask omega eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMaskSeamTransfer_pairSwitch mask omega eta

/--
[SixVertexFullDisagreementMask.pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma pairSwitch_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  SixVertexFullDisagreementMask (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) mask := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.pairSwitch hmask

/--
[SixVertexFullDisagreementMask.eq_fullDisagreementMask_switchFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma eq_fullDisagreementMask_switchFirst_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  mask = sixVertexFullDisagreementMask omega (sixVertexTorusSwitchFirst mask omega eta) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.eq_fullDisagreementMask_switchFirst hmask

/--
[sixVertexTorusSwitchFirst_injective_on_fullMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexTorusSwitchFirst_injective_on_fullMasks_eq
  {T : EvenTorus}
  {omega eta first second : SixVertexArrows T}
-- given
  (hfirst : SixVertexFullDisagreementMask omega eta first)
  (hsecond : SixVertexFullDisagreementMask omega eta second)
  (heq : sixVertexTorusSwitchFirst first omega eta = sixVertexTorusSwitchFirst second omega eta) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchFirst_injective_on_fullMasks hfirst hsecond heq

/--
[sixVertexPairUnionHorizontal_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexPairUnionHorizontal_pairSwitch_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexPairUnionHorizontal (omega, eta) = sixVertexPairUnionHorizontal (sixVertexTorusSwitchFirst mask omega eta, sixVertexTorusSwitchSecond mask omega eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnionHorizontal_pairSwitch mask omega eta

/--
[sixVertexPairUnionVertical_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexPairUnionVertical_pairSwitch_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexPairUnionVertical (omega, eta) = sixVertexPairUnionVertical (sixVertexTorusSwitchFirst mask omega eta, sixVertexTorusSwitchSecond mask omega eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairUnionVertical_pairSwitch mask omega eta

/--
[SixVertexFullDisagreementMask.pairAtMostTwoCycleFineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma pairAtMostTwoCycleFineRelated_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (omega, eta) (sixVertexTorusSwitchFirst mask omega eta, sixVertexTorusSwitchSecond mask omega eta) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.pairAtMostTwoCycleFineRelated hmask

/--
[sixVertexLexDisagreementComponentMask_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentMask_full_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  SixVertexFullDisagreementMask omega eta (sixVertexLexDisagreementComponentMask T omega eta h) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentMask_full T omega eta h

/--
[sixVertexLoopDecoratedFullMaskFineTarget_false_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedFullMaskFineTarget_false_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
-- imply
  (sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer).1 false).arrows = sixVertexTorusSwitchFirst mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedFullMaskFineTarget_false_arrows middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer

/--
[sixVertexLoopDecoratedFullMaskFineTarget_true_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedFullMaskFineTarget_true_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
-- imply
  (sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer).1 true).arrows = sixVertexTorusSwitchSecond mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedFullMaskFineTarget_true_arrows middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer

/--
[sixVertexLoopFullUnitMaskTarget_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullUnitMaskTarget_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  Function.Injective (sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt profile source) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullUnitMaskTarget_injective middle hmiddle_pos hmiddle_lt profile source

/--
[sixVertexLoopFullMaskFineRelated_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullMaskFineRelated_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
-- imply
  SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullMaskFineRelated_target middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer

/--
[sixVertexLoopDecoratedFullMaskFineTarget_lex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedFullMaskFineTarget_lex_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source.1) :
-- imply
  let h := sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos hmiddle_lt source.1 let mask := sixVertexLexDisagreementComponentMask T (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows h let hmask := sixVertexLexDisagreementComponentMask_full T (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows h sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt profile source mask hmask hunit = sixVertexLoopDecoratedUnitTransferFineTarget middle hmiddle_pos hmiddle_lt profile source hunit := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedFullMaskFineTarget_lex middle hmiddle_pos hmiddle_lt profile source hunit

/--
[sixVertexLoopLexUnitFineRelated_imp_fullMaskFineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopLexUnitFineRelated_imp_fullMaskFineRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopLexUnitFineRelated_imp_fullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullUnitMaskOfRelated_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullUnitMaskOfRelated_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  target = sixVertexLoopFullUnitMaskTarget middle hmiddle_pos hmiddle_lt profile source (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt profile source target hrelated) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullUnitMaskOfRelated_false_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullUnitMaskOfRelated_false_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt profile source target hrelated (sixVertexLoopDecoratedPairColored target.1 false).arrows = sixVertexTorusSwitchFirst certificate.1 (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullUnitMaskOfRelated_false_arrows middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullUnitMaskOfRelated_true_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullUnitMaskOfRelated_true_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt profile source target hrelated (sixVertexLoopDecoratedPairColored target.1 true).arrows = sixVertexTorusSwitchSecond certificate.1 (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullUnitMaskOfRelated_true_arrows middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullUnitMaskOfRelated_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullUnitMaskOfRelated_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt profile source target hrelated sixVertexLoopDecoratedPairColored target.1 = sixVertexFullDisagreementColoredTarget (sixVertexLoopDecoratedPairColored source.1) certificate.1 certificate.2.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullUnitMaskOfRelated_colored middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullNegativeMaskOfPreimage_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullNegativeMaskOfPreimage_val_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
  {preimage : {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile // SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target}}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos hmiddle_lt profile target preimage).1 = (sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullNegativeMaskOfPreimage_val middle hmiddle_pos hmiddle_lt profile target preimage

/--
[sixVertexLoopFullNegativeMaskOfPreimage_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullNegativeMaskOfPreimage_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  Function.Injective (sixVertexLoopFullNegativeMaskOfPreimage middle hmiddle_pos hmiddle_lt profile target) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullNegativeMaskOfPreimage_injective middle hmiddle_pos hmiddle_lt profile target

/--
[card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (Finset.univ.filter fun source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile => SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target).card <= Fintype.card (SixVertexLoopFullNegativeMask profile target) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLoopFullMaskFineRelated_preimages_le_negativeMasks middle hmiddle_pos hmiddle_lt profile target

/--
[card_sixVertexLoopFullMaskFineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma card_sixVertexLoopFullMaskFineRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (Finset.univ.filter (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source)).card = Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source

/--
[sixVertexLoopFullMaskFineRelated_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullMaskFineRelated_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source.1 false).arrows (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
-- imply
  (Finset.univ.filter (SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source)).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullMaskFineRelated_nonempty middle hmiddle_pos hmiddle_lt profile source mask hmask htransfer

/--
[sixVertexLoopFullMaskFineRelated_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullMaskFineRelated_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  sixVertexLoopDecoratedPairBigrade target.1 = sixVertexLoopDecoratedPairBigrade source.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullMaskFineRelated_bigrade middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopFullMaskFineRelated_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopFullMaskFineRelated_twoCycle_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((sixVertexLoopDecoratedPairColored source.1 false).arrows, (sixVertexLoopDecoratedPairColored source.1 true).arrows) ((sixVertexLoopDecoratedPairColored target.1 false).arrows, (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopFullMaskFineRelated_twoCycle middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[rawFineProfile_of_fullMaskUnitDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma rawFineProfile_of_fullMaskUnitDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source))
  (hdegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target -> (Finset.univ.filter fun otherSource => SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile otherSource target).card <= Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source)) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt hne hdegree

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskUnitDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskUnitDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source))
  (hdegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target -> (Finset.univ.filter fun otherSource => SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile otherSource target).card <= Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source)) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskUnitDegree middle hmiddle_pos hmiddle_lt hne hdegree

/--
[rawFineProfile_of_fullMaskNegativePositiveDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma rawFineProfile_of_fullMaskNegativePositiveDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source))
  (hmaskDegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target -> Fintype.card (SixVertexLoopFullNegativeMask profile target) <= Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source)) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_fullMaskNegativePositiveDegree middle hmiddle_pos hmiddle_lt hne hmaskDegree

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskNegativePositiveDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskNegativePositiveDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source))
  (hmaskDegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile source target -> Fintype.card (SixVertexLoopFullNegativeMask profile target) <= Fintype.card (SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source)) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_fullMaskNegativePositiveDegree middle hmiddle_pos hmiddle_lt hne hmaskDegree


-- created on 2026-10-23

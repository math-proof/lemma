import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
open Finset StatMech StatMech.FrontierD


/--
[sixVertexTorusSwitchFirst_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexTorusSwitchFirst_involutive_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchFirst mask (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) = omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchFirst_involutive mask omega eta

/--
[sixVertexTorusSwitchSecond_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexTorusSwitchSecond_involutive_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchSecond mask (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) = eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchSecond_involutive mask omega eta

/--
[intCast_sixVertexUpCount_verticalRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma intCast_sixVertexUpCount_verticalRow_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) = ∑ i : Fin T.width, ((omega.vertical (i, svFinLast T.height_pos)).toNat : Int) := by
-- proof
  apply StatMech.FrontierD.intCast_sixVertexUpCount_verticalRow omega

/--
[intCast_upCount_switchFirst_eq_add_seamTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma intCast_upCount_switchFirst_eq_add_seamTransfer_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T (sixVertexTorusSwitchFirst mask omega eta) (svFinLast T.height_pos)) : Int) = sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) + sixVertexTorusMaskSeamTransfer mask omega eta := by
-- proof
  apply StatMech.FrontierD.intCast_upCount_switchFirst_eq_add_seamTransfer mask omega eta

/--
[intCast_upCount_switchSecond_eq_sub_seamTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma intCast_upCount_switchSecond_eq_sub_seamTransfer_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T (sixVertexTorusSwitchSecond mask omega eta) (svFinLast T.height_pos)) : Int) = sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) - sixVertexTorusMaskSeamTransfer mask omega eta := by
-- proof
  apply StatMech.FrontierD.intCast_upCount_switchSecond_eq_sub_seamTransfer mask omega eta

/--
[two_le_card_sixVertexPositiveSeamDisagreements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma two_le_card_sixVertexPositiveSeamDisagreements_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  2 <= (sixVertexPositiveSeamDisagreements T omega eta).card := by
-- proof
  apply StatMech.FrontierD.two_le_card_sixVertexPositiveSeamDisagreements T omega eta n homegaSector hetaSector hn

/--
[exists_two_positiveSeamDisagreements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma exists_two_positiveSeamDisagreements_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  exists i j : Fin T.width, i ≠ j /\ i ∈ sixVertexPositiveSeamDisagreements T omega eta /\ j ∈ sixVertexPositiveSeamDisagreements T omega eta := by
-- proof
  apply StatMech.FrontierD.exists_two_positiveSeamDisagreements T omega eta n homegaSector hetaSector hn

/--
[sixVertexTorusSwitchFirst_fullDisagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexTorusSwitchFirst_fullDisagreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchFirst (sixVertexFullDisagreementMask omega eta) omega eta = eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchFirst_fullDisagreement omega eta

/--
[sixVertexTorusSwitchSecond_fullDisagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexTorusSwitchSecond_fullDisagreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchSecond (sixVertexFullDisagreementMask omega eta) omega eta = omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchSecond_fullDisagreement omega eta

/--
[sixVertexFullDisagreementMask_seamTransfer_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexFullDisagreementMask_seamTransfer_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  sixVertexTorusMaskSeamTransfer (sixVertexFullDisagreementMask omega eta) omega eta = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFullDisagreementMask_seamTransfer_eq_two omega eta n homegaSector hetaSector hn

/--
[sixVertexLexDisagreementComponentSwitch_local_eq_or_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_local_eq_or_swap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v, sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v) = (sixVertexLocalIncomingPattern omega v, sixVertexLocalIncomingPattern eta v) \/ (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v, sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v) = (sixVertexLocalIncomingPattern eta v, sixVertexLocalIncomingPattern omega v) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_local_eq_or_swap T omega eta h v

/--
[sixVertexLexDisagreementComponentSwitch_localCTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_localCTypeCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexLocalCTypeCount (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v) (sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) v) = sixVertexLocalCTypeCount (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_localCTypeCount T omega eta h v

/--
[sixVertexLexDisagreementComponentSwitch_totalCTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_totalCTypeCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexTorusCTypeCount (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) + sixVertexTorusCTypeCount (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) = sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_totalCTypeCount T omega eta h

/--
[sixVertexLexDisagreementComponentSwitch_multiplicityNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_multiplicityNat_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexMarkedPairMultiplicityNat (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) k = sixVertexMarkedPairMultiplicityNat omega eta k := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_multiplicityNat T omega eta h k

/--
[sixVertexLexDisagreementComponentSwitch_markedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_markedWeight_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexTorusMarkedWeight (sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) * sixVertexTorusMarkedWeight (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta) = sixVertexTorusMarkedWeight omega * sixVertexTorusMarkedWeight eta := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_markedWeight T omega eta homega heta h

/--
[sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentCType.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (htransfer : sixVertexTorusMaskSeamTransfer (sixVertexLexDisagreementComponentMask T omega eta h) omega eta = 1) :
-- imply
  let first := sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta let second := sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta first.IceRule /\ second.IceRule /\ sixVertexUpCount (svTorusVerticalRows T first (svFinLast T.height_pos)) = n /\ sixVertexUpCount (svTorusVerticalRows T second (svFinLast T.height_pos)) = n := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_to_middle_of_transfer_one T omega eta n homega heta homegaSector hetaSector hn h htransfer


-- created on 2026-10-23

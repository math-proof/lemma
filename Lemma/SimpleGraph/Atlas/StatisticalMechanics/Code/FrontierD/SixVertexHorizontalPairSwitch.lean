import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalZeroCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalZeroCount_eq_sum_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalZeroCount horizontal = ∑ v : T.Vertex, if sixVertexHorizontalGaugeBit horizontal v = false then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalZeroCount_eq_sum horizontal

/--
[sixVertexSwitchHorizontalPair_zeroCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_zeroCount_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalZeroCount (sixVertexSwitchHorizontalPair mask horizontal).1 + sixVertexHorizontalZeroCount (sixVertexSwitchHorizontalPair mask horizontal).2 = sixVertexHorizontalZeroCount horizontal.1 + sixVertexHorizontalZeroCount horizontal.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_zeroCount mask horizontal

/--
[sixVertexSwitchHorizontalPair_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_involutive_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool) :
-- imply
  Function.Involutive (sixVertexSwitchHorizontalPair (T := T) mask) := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_involutive mask

/--
[boolPairAgreementCount_eq_cross_of_left_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma boolPairAgreementCount_eq_cross_of_left_eq_eq
  {a b c d : Bool}
-- given
  (h : a = b) :
-- imply
  boolPairAgreementCount a b c d = boolPairCrossAgreementCount a b c d := by
-- proof
  apply StatMech.FrontierD.boolPairAgreementCount_eq_cross_of_left_eq h

/--
[boolPairAgreementCount_eq_cross_of_right_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma boolPairAgreementCount_eq_cross_of_right_eq_eq
  {a b c d : Bool}
-- given
  (h : c = d) :
-- imply
  boolPairAgreementCount a b c d = boolPairCrossAgreementCount a b c d := by
-- proof
  apply StatMech.FrontierD.boolPairAgreementCount_eq_cross_of_right_eq h

/--
[boolPairAgreementCount_add_cross_of_mixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma boolPairAgreementCount_add_cross_of_mixed_eq
  {a b c d : Bool}
-- given
  (hab : a ≠ b)
  (hcd : c ≠ d) :
-- imply
  boolPairAgreementCount a b c d + boolPairCrossAgreementCount a b c d = 2 := by
-- proof
  apply StatMech.FrontierD.boolPairAgreementCount_add_cross_of_mixed hab hcd

/--
[sixVertexHorizontalPair_nontransitionCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexHorizontalPair_nontransitionCount_eq_sum_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalNontransitionCount horizontal.1 + sixVertexHorizontalNontransitionCount horizontal.2 = ∑ v : T.Vertex, sixVertexHorizontalPairBondAgreementCount horizontal v := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPair_nontransitionCount_eq_sum horizontal

/--
[sixVertexSwitchHorizontalPair_bondAgreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_bondAgreement_eq
  {T : EvenTorus}
  {v : T.Vertex}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBondAgreementCount (sixVertexSwitchHorizontalPair mask horizontal) v = if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1 then sixVertexHorizontalPairBondAgreementCount horizontal v else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_bondAgreement mask horizontal v

/--
[sixVertexSwitchHorizontalPair_nontransitionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_nontransitionCount_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalNontransitionCount (sixVertexSwitchHorizontalPair mask horizontal).1 + sixVertexHorizontalNontransitionCount (sixVertexSwitchHorizontalPair mask horizontal).2 = ∑ v : T.Vertex, if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1 then sixVertexHorizontalPairBondAgreementCount horizontal v else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_nontransitionCount mask horizontal

/--
[sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hbalanced : SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
-- imply
  sixVertexHorizontalNontransitionCount (sixVertexSwitchHorizontalPair mask horizontal).1 + sixVertexHorizontalNontransitionCount (sixVertexSwitchHorizontalPair mask horizontal).2 = sixVertexHorizontalNontransitionCount horizontal.1 + sixVertexHorizontalNontransitionCount horizontal.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced mask horizontal hbalanced

/--
[sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hbalanced : SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexSwitchHorizontalPair mask horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced mask horizontal hbalanced


-- created on 2026-10-23

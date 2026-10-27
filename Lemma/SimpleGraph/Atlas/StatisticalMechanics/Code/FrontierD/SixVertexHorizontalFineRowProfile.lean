import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalRowZeroCount_le_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalRowZeroCount_le_width_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalRowZeroCount horizontal j <= T.width := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalRowZeroCount_le_width horizontal j

/--
[sixVertexHorizontalRowNontransitionCount_le_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalRowNontransitionCount_le_width_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalRowNontransitionCount horizontal j <= T.width := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalRowNontransitionCount_le_width horizontal j

/--
[sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq_eq
  {T : EvenTorus}
  {first second : SixVertexHorizontalField T × SixVertexHorizontalField T}
-- given
  (h : sixVertexHorizontalPairFineRowProfile first = sixVertexHorizontalPairFineRowProfile second) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile first = sixVertexHorizontalPairBoundedFineRowProfile second := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq h

/--
[sum_sixVertexHorizontalRowNontransitionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sum_sixVertexHorizontalRowNontransitionCount_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  (∑ j : Fin T.height, sixVertexHorizontalRowNontransitionCount horizontal j) = sixVertexHorizontalNontransitionCount horizontal := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexHorizontalRowNontransitionCount horizontal

/--
[sum_sixVertexHorizontalPairRowNontransitionProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sum_sixVertexHorizontalPairRowNontransitionProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  (∑ j : Fin T.height, sixVertexHorizontalPairRowNontransitionProfile horizontal j) = sixVertexHorizontalNontransitionCount horizontal.1 + sixVertexHorizontalNontransitionCount horizontal.2 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexHorizontalPairRowNontransitionProfile horizontal

/--
[sixVertexHorizontalRowNontransitionCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalRowNontransitionCount_reflect_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalRowNontransitionCount (sixVertexReflectHorizontalField horizontal) j = sixVertexHorizontalRowNontransitionCount horizontal j := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalRowNontransitionCount_reflect horizontal j

/--
[sixVertexHorizontalPairRowNontransitionProfile_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalPairRowNontransitionProfile_eq_sum_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowNontransitionProfile horizontal j = ∑ i : Fin T.width, sixVertexHorizontalPairBondAgreementCount horizontal (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairRowNontransitionProfile_eq_sum horizontal j

/--
[sixVertexSwitchHorizontalPair_rowNontransitionProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowNontransitionProfile (sixVertexSwitchHorizontalPair mask horizontal) j = ∑ i : Fin T.width, if mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i then sixVertexHorizontalPairBondAgreementCount horizontal (i, j) else sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_rowNontransitionProfile mask horizontal j

/--
[sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hbalanced : SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
-- imply
  sixVertexHorizontalPairRowNontransitionProfile (sixVertexSwitchHorizontalPair mask horizontal) = sixVertexHorizontalPairRowNontransitionProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced mask horizontal hbalanced

/--
[sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hbalanced : SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
-- imply
  sixVertexHorizontalPairFineRowProfile (sixVertexSwitchHorizontalPair mask horizontal) = sixVertexHorizontalPairFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced mask horizontal hbalanced

/--
[sixVertexSwitchHorizontalPair_boundedFineRowProfile_of_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_boundedFineRowProfile_of_balanced_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hbalanced : SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (sixVertexSwitchHorizontalPair mask horizontal) = sixVertexHorizontalPairBoundedFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_boundedFineRowProfile_of_balanced mask horizontal hbalanced

/--
[sixVertexReflectFirstHorizontalLayer_fineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexReflectFirstHorizontalLayer_fineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairFineRowProfile (sixVertexReflectFirstHorizontalLayer horizontal) = sixVertexHorizontalPairFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectFirstHorizontalLayer_fineRowProfile horizontal

/--
[sixVertexReflectFirstHorizontalLayer_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexReflectFirstHorizontalLayer_boundedFineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (sixVertexReflectFirstHorizontalLayer horizontal) = sixVertexHorizontalPairBoundedFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectFirstHorizontalLayer_boundedFineRowProfile horizontal

/--
[sixVertexReflectSecondHorizontalLayer_fineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexReflectSecondHorizontalLayer_fineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairFineRowProfile (sixVertexReflectSecondHorizontalLayer horizontal) = sixVertexHorizontalPairFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectSecondHorizontalLayer_fineRowProfile horizontal

/--
[sixVertexReflectSecondHorizontalLayer_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexReflectSecondHorizontalLayer_boundedFineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (sixVertexReflectSecondHorizontalLayer horizontal) = sixVertexHorizontalPairBoundedFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectSecondHorizontalLayer_boundedFineRowProfile horizontal

/--
[sixVertexSwapHorizontalLayers_fineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwapHorizontalLayers_fineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairFineRowProfile (sixVertexSwapHorizontalLayers horizontal) = sixVertexHorizontalPairFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapHorizontalLayers_fineRowProfile horizontal

/--
[sixVertexSwapHorizontalLayers_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexSwapHorizontalLayers_boundedFineRowProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (sixVertexSwapHorizontalLayers horizontal) = sixVertexHorizontalPairBoundedFineRowProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapHorizontalLayers_boundedFineRowProfile horizontal

/--
[rowProfileSignedNonnegative_of_fineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma rowProfileSignedNonnegative_of_fineRowProfile_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  SixVertexHorizontalRowProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.rowProfileSignedNonnegative_of_fineRowProfile T sourceLeft sourceRight targetLeft targetRight hfine

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfine : SixVertexHorizontalFineRowProfileAggregateSignedNonnegative T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_fineRowProfileSigned T middle hmiddle_pos hmiddle_lt hfine


-- created on 2026-10-23

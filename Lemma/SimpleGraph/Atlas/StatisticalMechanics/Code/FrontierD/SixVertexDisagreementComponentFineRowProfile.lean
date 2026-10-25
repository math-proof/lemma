import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentFineRowProfile
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {j : Fin T.height} :
-- imply
  sixVertexHorizontalRowNontransitionCount omega.horizontal j = ∑ i : Fin T.width, if omega.IsCType (i, j) then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalRowNontransitionCount_eq_rowCTypeCount omega j

/--
[sixVertexTorusPairSwitch_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma sixVertexTorusPairSwitch_rowZeroProfile_eq
  {T : EvenTorus}
  {mask omega eta : SixVertexArrows T} :
-- imply
  sixVertexHorizontalPairRowZeroProfile ((sixVertexTorusSwitchFirst mask omega eta).horizontal, (sixVertexTorusSwitchSecond mask omega eta).horizontal) = sixVertexHorizontalPairRowZeroProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusPairSwitch_rowZeroProfile mask omega eta

/--
[sixVertexLexDisagreementComponentSwitch_rowNontransitionProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_rowNontransitionProfile_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexHorizontalPairRowNontransitionProfile ((sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal, (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal) = sixVertexHorizontalPairRowNontransitionProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_rowNontransitionProfile T omega eta h

/--
[sixVertexLexDisagreementComponentSwitch_fineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_fineRowProfile_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexHorizontalPairFineRowProfile ((sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal, (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal) = sixVertexHorizontalPairFineRowProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_fineRowProfile T omega eta h

/--
[sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal, (sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T omega eta h) omega eta).horizontal) = sixVertexHorizontalPairBoundedFineRowProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentSwitch_boundedFineRowProfile T omega eta h

/--
[exists_middle_pair_same_boundedFineRowProfile_of_componentTransfer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentFineRowProfile.lean)
-/
@[path]
private lemma exists_middle_pair_same_boundedFineRowProfile_of_componentTransfer_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (htransfer : sixVertexTorusMaskSeamTransfer (sixVertexLexDisagreementComponentMask T omega eta h) omega eta = 1) :
-- imply
  exists first second : SixVertexArrows T, first.IceRule /\ second.IceRule /\ sixVertexUpCount (svTorusVerticalRows T first (svFinLast T.height_pos)) = middle /\ sixVertexUpCount (svTorusVerticalRows T second (svFinLast T.height_pos)) = middle /\ sixVertexHorizontalPairBoundedFineRowProfile (first.horizontal, second.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.exists_middle_pair_same_boundedFineRowProfile_of_componentTransfer_one T omega eta middle homega heta homegaSector hetaSector hmiddle h htransfer


-- created on 2026-10-23

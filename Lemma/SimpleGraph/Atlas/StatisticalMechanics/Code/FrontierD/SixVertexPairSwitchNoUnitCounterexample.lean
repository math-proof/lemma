import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
open Finset StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoLowArrows_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoLowArrows_ice_eq :
-- imply
  sixVertexFourByTwoLowArrows.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoLowArrows_ice

/--
[sixVertexFourByTwoHighArrows_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoHighArrows_ice_eq :
-- imply
  sixVertexFourByTwoHighArrows.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoHighArrows_ice

/--
[sixVertexFourByTwoLowArrows_seamCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoLowArrows_seamCount_eq :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus sixVertexFourByTwoLowArrows (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoLowArrows_seamCount

/--
[sixVertexFourByTwoHighArrows_seamCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwoHighArrows_seamCount_eq :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus sixVertexFourByTwoHighArrows (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoHighArrows_seamCount

/--
[sixVertexFourByTwo_localDisagreementDegree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_localDisagreementDegree_two_eq
  {v : sixVertexFourByTwoTorus.Vertex} :
-- imply
  (∑ d, if sixVertexLocalIncomingPattern sixVertexFourByTwoLowArrows v d ≠ sixVertexLocalIncomingPattern sixVertexFourByTwoHighArrows v d then 1 else 0) = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_localDisagreementDegree_two v

/--
[sixVertexFourByTwo_switchFirst_eq_reduced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_switchFirst_eq_reduced_eq
  {mask : SixVertexArrows sixVertexFourByTwoTorus} :
-- imply
  sixVertexTorusSwitchFirst mask sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows = sixVertexFourByTwoReducedArrows (sixVertexFourByTwoReducedMaskOf mask) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_switchFirst_eq_reduced mask

/--
[sixVertexFourByTwo_reduced_no_ice_to_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_reduced_no_ice_to_middle_eq
  {r : SixVertexFourByTwoReducedMask} :
-- imply
  ¬ ((sixVertexFourByTwoReducedArrows r).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoReducedArrows r) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_reduced_no_ice_to_middle r

/--
[sixVertexFourByTwo_no_icePairSwitch_to_middle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean)
-/
@[path]
private lemma sixVertexFourByTwo_no_icePairSwitch_to_middle_eq
  {mask : SixVertexArrows sixVertexFourByTwoTorus} :
-- imply
  ¬ ((sixVertexTorusSwitchFirst mask sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows).IceRule /\ (sixVertexTorusSwitchSecond mask sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexTorusSwitchFirst mask sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_no_icePairSwitch_to_middle mask


-- created on 2026-10-23

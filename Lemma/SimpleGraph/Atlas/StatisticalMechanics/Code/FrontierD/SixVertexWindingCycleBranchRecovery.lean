import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexSignedWindingCycleTarget


/--
[swapTarget_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma swapTarget_target_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign} :
-- imply
  branch.swapTarget.target = (branch.target.2, branch.target.1) := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.swapTarget_target branch

/--
[target_ne_swapTarget_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma target_ne_swapTarget_iff_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign} :
-- imply
  branch.target ≠ branch.swapTarget.target ↔ branch.target.1 ≠ branch.target.2 := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.target_ne_swapTarget_iff branch

/--
[related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma related_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign} :
-- imply
  sixVertexPairAtMostTwoCycleRelated source branch.target := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.related branch

/--
[recover_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma recover_target_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign} :
-- imply
  branch.recover.target = source := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.recover_target branch

/--
[target_ne_source_of_horizontalFlow_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma target_ne_source_of_horizontalFlow_ne_zero_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign}
  {v : T.Vertex}
-- given
  (hflow : family.horizontalFlow v ≠ 0) :
-- imply
  branch.target ≠ source := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.target_ne_source_of_horizontalFlow_ne_zero branch v hflow

/--
[target_ne_source_of_verticalFlow_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma target_ne_source_of_verticalFlow_ne_zero_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {sign : Bool}
  {branch : SixVertexSignedWindingCycleTarget source family sign}
  {v : T.Vertex}
-- given
  (hflow : family.verticalFlow v ≠ 0) :
-- imply
  branch.target ≠ source := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.target_ne_source_of_verticalFlow_ne_zero branch v hflow

/--
[targets_ne_of_signedHorizontalFlow_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma targets_ne_of_signedHorizontalFlow_ne_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {firstFamily secondFamily : SixVertexAtMostTwoCycleFamily T}
  {firstSign secondSign : Bool}
  {first : SixVertexSignedWindingCycleTarget source firstFamily firstSign}
  {second : SixVertexSignedWindingCycleTarget source secondFamily secondSign}
  {v : T.Vertex}
-- given
  (hflow : (if firstSign then firstFamily.horizontalFlow v else -firstFamily.horizontalFlow v) ≠ if secondSign then secondFamily.horizontalFlow v else -secondFamily.horizontalFlow v) :
-- imply
  first.target ≠ second.target := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.targets_ne_of_signedHorizontalFlow_ne first second v hflow

/--
[targets_ne_of_signedVerticalFlow_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma targets_ne_of_signedVerticalFlow_ne_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {firstFamily secondFamily : SixVertexAtMostTwoCycleFamily T}
  {firstSign secondSign : Bool}
  {first : SixVertexSignedWindingCycleTarget source firstFamily firstSign}
  {second : SixVertexSignedWindingCycleTarget source secondFamily secondSign}
  {v : T.Vertex}
-- given
  (hflow : (if firstSign then firstFamily.verticalFlow v else -firstFamily.verticalFlow v) ≠ if secondSign then secondFamily.verticalFlow v else -secondFamily.verticalFlow v) :
-- imply
  first.target ≠ second.target := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.targets_ne_of_signedVerticalFlow_ne first second v hflow

/--
[opposite_targets_ne_of_horizontalFlow_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma opposite_targets_ne_of_horizontalFlow_ne_zero_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {negative : SixVertexSignedWindingCycleTarget source family false}
  {positive : SixVertexSignedWindingCycleTarget source family true}
  {v : T.Vertex}
-- given
  (hflow : family.horizontalFlow v ≠ 0) :
-- imply
  negative.target ≠ positive.target := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.opposite_targets_ne_of_horizontalFlow_ne_zero negative positive v hflow

/--
[opposite_targets_ne_of_verticalFlow_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean)
-/
@[path]
private lemma opposite_targets_ne_of_verticalFlow_ne_zero_eq
  {T : EvenTorus}
  {source : SixVertexArrows T × SixVertexArrows T}
  {family : SixVertexAtMostTwoCycleFamily T}
  {negative : SixVertexSignedWindingCycleTarget source family false}
  {positive : SixVertexSignedWindingCycleTarget source family true}
  {v : T.Vertex}
-- given
  (hflow : family.verticalFlow v ≠ 0) :
-- imply
  negative.target ≠ positive.target := by
-- proof
  apply StatMech.FrontierD.SixVertexSignedWindingCycleTarget.opposite_targets_ne_of_verticalFlow_ne_zero negative positive v hflow


-- created on 2026-10-23

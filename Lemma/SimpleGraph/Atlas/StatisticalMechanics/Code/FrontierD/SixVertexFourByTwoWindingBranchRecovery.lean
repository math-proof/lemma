import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoWindingBranchRecovery
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoBottomCycleFamily_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoWindingBranchRecovery.lean)
-/
@[path]
private lemma sixVertexFourByTwoBottomCycleFamily_nonzero_eq :
-- imply
  sixVertexFourByTwoBottomCycleFamily.horizontalFlow (sixVertexFourByTwoVertex 0 0) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoBottomCycleFamily_nonzero

/--
[sixVertexFourByTwoObstructionWindingTarget_ne_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoWindingBranchRecovery.lean)
-/
@[path]
private lemma sixVertexFourByTwoObstructionWindingTarget_ne_source_eq :
-- imply
  sixVertexFourByTwoObstructionWindingTarget.target ≠ (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoObstructionWindingTarget_ne_source

/--
[sixVertexFourByTwoObstructionWindingTarget_recovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoWindingBranchRecovery.lean)
-/
@[path]
private lemma sixVertexFourByTwoObstructionWindingTarget_recovers_eq :
-- imply
  sixVertexFourByTwoObstructionWindingTarget.recover.target = (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoObstructionWindingTarget_recovers


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamVerticalNoGo
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwo_no_positiveVerticalWindingTargetIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamVerticalNoGo.lean)
-/
@[path]
private lemma sixVertexFourByTwo_no_positiveVerticalWindingTargetIndex_eq
  {column : Fin sixVertexFourByTwoTorus.width}
  {target : Fin 28 × Fin 28} :
-- imply
  ¬ (sixVertexPairUnionHorizontalDelta (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) (sixVertexFourByTwoTargetIndexArrows target) = (sixVertexPositiveVerticalWindingFamily column).horizontalFlow ∧ sixVertexPairUnionVerticalDelta (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) (sixVertexFourByTwoTargetIndexArrows target) = (sixVertexPositiveVerticalWindingFamily column).verticalFlow) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_no_positiveVerticalWindingTargetIndex column target


-- created on 2026-10-23

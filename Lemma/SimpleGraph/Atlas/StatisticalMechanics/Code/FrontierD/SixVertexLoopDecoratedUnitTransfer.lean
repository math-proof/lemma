import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexLoopDecoratedUnitTransfer
open StatMech StatMech.FrontierD


/--
[sixVertexLoopDecoratedUnitTransferTarget_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopDecoratedUnitTransfer.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedUnitTransferTarget_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source) :
-- imply
  sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedUnitTransferTarget middle hmiddle_pos hmiddle_lt source hunit) = sixVertexLexDisagreementComponentColoredTarget (sixVertexLoopDecoratedPairColored source) (sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos hmiddle_lt source) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedUnitTransferTarget_colored middle hmiddle_pos hmiddle_lt source hunit

/--
[sixVertexLoopDecoratedUnitTransferTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopDecoratedUnitTransfer.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedUnitTransferTarget_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source) :
-- imply
  sixVertexLoopDecoratedPairBigrade (sixVertexLoopDecoratedUnitTransferTarget middle hmiddle_pos hmiddle_lt source hunit) = sixVertexLoopDecoratedPairBigrade source := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedUnitTransferTarget_bigrade middle hmiddle_pos hmiddle_lt source hunit


-- created on 2026-10-23

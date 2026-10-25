import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveSeamDecodedLoopHall.Part2
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection


/--
[source_recoverable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean)
-/
@[path]
private lemma source_recoverable_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection T middle hmiddle_pos hmiddle_lt grade}
  {first second : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {firstBranch secondBranch : Bool}
-- given
  (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first (data.key first firstBranch) = sixVertexHorizontalDegreeTwoLoopRoutedTarget second (data.key second secondBranch)) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection.source_recoverable data first second firstBranch secondBranch heq

/--
[high_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean)
-/
@[path]
private lemma high_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {data : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (data.key source.1 false) ≠ sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (data.key source.1 true) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnection.high_distinct data source

/--
[degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean)
-/
@[path]
private lemma degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopRoutedReconnections_of_decodedWindingReconnections T middle hmiddle_pos hmiddle_lt hdecoded

/--
[loopBigradeFibers_of_decodedWindingReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean)
-/
@[path]
private lemma loopBigradeFibers_of_decodedWindingReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexLoopDecoratedPairBigradeFiberDominates T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle := by
-- proof
  apply StatMech.FrontierD.loopBigradeFibers_of_decodedWindingReconnections T middle hmiddle_pos hmiddle_lt hdecoded

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedWindingReconnections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveSeamDecodedLoopHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedWindingReconnections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hdecoded : SixVertexHorizontalDegreeTwoLoopDecodedWindingReconnections T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedWindingReconnections T middle hmiddle_pos hmiddle_lt hdecoded


-- created on 2026-10-23

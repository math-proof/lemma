import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRepairDecodedLoopHall.Part2
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair


/--
[source_recoverable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean)
-/
@[path]
private lemma source_recoverable_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair T middle hmiddle_pos hmiddle_lt grade}
  {first second : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {firstBranch secondBranch : Bool}
-- given
  (heq : sixVertexHorizontalDegreeTwoLoopRoutedTarget first (data.key first firstBranch) = sixVertexHorizontalDegreeTwoLoopRoutedTarget second (data.key second secondBranch)) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair.source_recoverable data first second firstBranch secondBranch heq

/--
[high_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean)
-/
@[path]
private lemma high_distinct_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {data : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair T middle hmiddle_pos hmiddle_lt grade}
  {source : SixVertexHorizontalDegreeTwoLoopHighChargeSources T middle hmiddle_pos hmiddle_lt grade} :
-- imply
  sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (data.key source.1 false) ≠ sixVertexHorizontalDegreeTwoLoopRoutedTarget source.1 (data.key source.1 true) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepair.high_distinct data source

/--
[degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean)
-/
@[path]
private lemma degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalDegreeTwoLoopRoutedReconnections T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.degreeTwoLoopRoutedReconnections_of_decodedHorizontalRepairs T middle hmiddle_pos hmiddle_lt hrepairs

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedHorizontalRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRepairDecodedLoopHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedHorizontalRepairs_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrepairs : SixVertexHorizontalDegreeTwoLoopDecodedHorizontalRepairs T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_decodedHorizontalRepairs T middle hmiddle_pos hmiddle_lt hrepairs


-- created on 2026-10-23

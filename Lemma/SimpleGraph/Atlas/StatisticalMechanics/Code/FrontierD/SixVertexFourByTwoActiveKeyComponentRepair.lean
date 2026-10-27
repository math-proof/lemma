import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyComponentRepair
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoActiveObstructionCycleRepairComponents_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyComponentRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCycleRepairComponents_supported_eq :
-- imply
  SixVertexPairFineUnionKeyTwoCycleRelated sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCycleRepairComponents_supported

/--
[sixVertexFourByTwoActiveObstructionCycleRepairComponents_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyComponentRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCycleRepairComponents_reconnect_eq
  {source : SixVertexHorizontalActualDeficitFineUnionKeyFiber sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey} :
-- imply
  sixVertexFourByTwoActiveObstructionCycleRepairComponents.reconnect source = sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCycleRepairComponents_reconnect source

/--
[sixVertexFourByTwoActiveObstructionCycleRepairComponents_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyComponentRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCycleRepairComponents_embedding_eq :
-- imply
  sixVertexFourByTwoActiveObstructionCycleRepairComponents.toEmbedding = sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCycleRepairComponents_embedding


-- created on 2026-10-23

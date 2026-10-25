import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoMiddleArrows_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwoMiddleArrows_ice_eq :
-- imply
  sixVertexFourByTwoMiddleArrows.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMiddleArrows_ice

/--
[sixVertexFourByTwoMiddleArrows_seamCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwoMiddleArrows_seamCount_eq :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus sixVertexFourByTwoMiddleArrows (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMiddleArrows_seamCount

/--
[sixVertexFourByTwoLowArrows_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwoLowArrows_cTypeCount_eq :
-- imply
  sixVertexTorusCTypeCount sixVertexFourByTwoLowArrows = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoLowArrows_cTypeCount

/--
[sixVertexFourByTwoHighArrows_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwoHighArrows_cTypeCount_eq :
-- imply
  sixVertexTorusCTypeCount sixVertexFourByTwoHighArrows = 8 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoHighArrows_cTypeCount

/--
[sixVertexFourByTwoMiddleArrows_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwoMiddleArrows_cTypeCount_eq :
-- imply
  sixVertexTorusCTypeCount sixVertexFourByTwoMiddleArrows = 4 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMiddleArrows_cTypeCount

/--
[sixVertexFourByTwo_reconnection_markedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwo_reconnection_markedWeight_eq :
-- imply
  sixVertexTorusMarkedWeight sixVertexFourByTwoLowArrows * sixVertexTorusMarkedWeight sixVertexFourByTwoHighArrows = sixVertexTorusMarkedWeight sixVertexFourByTwoMiddleArrows * sixVertexTorusMarkedWeight sixVertexFourByTwoMiddleArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_reconnection_markedWeight

/--
[sixVertexFourByTwo_reconnection_multiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwo_reconnection_multiplicity_eq
  {k : Nat} :
-- imply
  sixVertexMarkedPairMultiplicity sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows k = sixVertexMarkedPairMultiplicity sixVertexFourByTwoMiddleArrows sixVertexFourByTwoMiddleArrows k := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_reconnection_multiplicity k

/--
[sixVertexFourByTwo_exists_weightPreserving_reconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean)
-/
@[path]
private lemma sixVertexFourByTwo_exists_weightPreserving_reconnection_eq :
-- imply
  exists alpha beta : SixVertexArrows sixVertexFourByTwoTorus, alpha.IceRule /\ beta.IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus alpha (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus beta (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\ sixVertexTorusMarkedWeight sixVertexFourByTwoLowArrows * sixVertexTorusMarkedWeight sixVertexFourByTwoHighArrows = sixVertexTorusMarkedWeight alpha * sixVertexTorusMarkedWeight beta := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_exists_weightPreserving_reconnection


-- created on 2026-10-23

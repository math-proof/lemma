import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKLoopSixVertexLocalCorrespondence.Part5
open Finset Matrix StatMech StatMech.FrontierD


/--
[incomingCount_eq_two_of_fkLoopPairingCompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma incomingCount_eq_two_of_fkLoopPairingCompatible_eq
  {pairing : Bool}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (h : fkLoopPairingCompatible pairing omega v) :
-- imply
  omega.incomingCount v = 2 := by
-- proof
  apply StatMech.FrontierD.incomingCount_eq_two_of_fkLoopPairingCompatible pairing omega v h

/--
[sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight_eq
  {lam : Real}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (∑ pairing : Bool, fkOrientedLoopLocalWeight lam pairing omega v) = omega.localWeight (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
-- proof
  apply StatMech.FrontierD.sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight lam omega v

/--
[fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum_eq
  {T : EvenTorus}
  {lam : Real} :
-- imply
  fkOrientedLoopPartitionSum T lam = sixVertexTorusArrowPartitionSum T (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum T lam

/--
[FKOrientedMedialLoops.toSixVertexConfiguration_seamUpCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma toSixVertexConfiguration_seamUpCount_eq
  {loops : FKOrientedMedialLoops T} :
-- imply
  sixVertexUpCount (svTorusVerticalRows T loops.toSixVertexConfiguration.1 (svFinLast T.height_pos)) = loops.seamUpCount := by
-- proof
  apply StatMech.FrontierD.FKOrientedMedialLoops.toSixVertexConfiguration_seamUpCount loops

/--
[fkOrientedLoopSectorPartitionSum_eq_sixVertexSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma fkOrientedLoopSectorPartitionSum_eq_sixVertexSector_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {lam : Real} :
-- imply
  fkOrientedLoopSectorPartitionSum T n lam = svTorusSectorArrowPartitionSum T n (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopSectorPartitionSum_eq_sixVertexSector T n lam

/--
[fkOrientedLoopFixedChargePartitionSum_eq_sectorTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKLoopSixVertexLocalCorrespondence.lean)
-/
@[path]
private lemma fkOrientedLoopFixedChargePartitionSum_eq_sectorTrace_eq
  {T : EvenTorus}
  {r : Nat}
  {lam : Real}
-- given
  (_hr : r <= T.width / 2) :
-- imply
  fkOrientedLoopSectorPartitionSum T ⟨T.width / 2 - r, Nat.lt_succ_of_le ((Nat.sub_le _ _).trans (Nat.div_le_self T.width 2))⟩ lam = Matrix.trace (sixVertexSectorTransfer T.width (T.width / 2 - r) (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ T.height) := by
-- proof
  apply StatMech.FrontierD.fkOrientedLoopFixedChargePartitionSum_eq_sectorTrace T r _hr lam


-- created on 2026-10-23

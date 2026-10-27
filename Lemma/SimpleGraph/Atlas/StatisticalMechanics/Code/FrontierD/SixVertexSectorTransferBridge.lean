import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorTransferBridge.Part2
open Finset Matrix StatMech StatMech.FrontierD


/--
[svTorusSectorArrowPartitionSum_eq_rowSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean)
-/
@[path]
private lemma svTorusSectorArrowPartitionSum_eq_rowSum_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {c : Real} :
-- imply
  svTorusSectorArrowPartitionSum T n c = ∑ vrows : Fin T.height -> SixVertexRow T.width, if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then ∏ j : Fin T.height, sixVertexTransfer T.width c (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j) else 0 := by
-- proof
  apply StatMech.FrontierD.svTorusSectorArrowPartitionSum_eq_rowSum T n c

/--
[svTorusSectorArrowPartitionSum_eq_sectorTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean)
-/
@[path]
private lemma svTorusSectorArrowPartitionSum_eq_sectorTrace_eq
  {T : EvenTorus}
  {n : Fin (T.width + 1)}
  {c : Real} :
-- imply
  svTorusSectorArrowPartitionSum T n c = Matrix.trace (sixVertexSectorTransfer T.width n c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.svTorusSectorArrowPartitionSum_eq_sectorTrace T n c

/--
[svTorusBalancedArrowPartitionSum_eq_sectorArrowPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean)
-/
@[path]
private lemma svTorusBalancedArrowPartitionSum_eq_sectorArrowPartitionSum_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  svTorusBalancedArrowPartitionSum T c = svTorusSectorArrowPartitionSum T ⟨T.width / 2, Nat.lt_succ_of_le (Nat.div_le_self T.width 2)⟩ c := by
-- proof
  apply StatMech.FrontierD.svTorusBalancedArrowPartitionSum_eq_sectorArrowPartitionSum T c

/--
[sixVertexTorusFixedChargePartitionSum_eq_sectorTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorTransferBridge.lean)
-/
@[path]
private lemma sixVertexTorusFixedChargePartitionSum_eq_sectorTrace_eq
  {T : EvenTorus}
  {r : Nat}
  {c : Real}
-- given
  (hr : r <= T.width / 2) :
-- imply
  sixVertexTorusFixedChargePartitionSum T r hr c = Matrix.trace (sixVertexSectorTransfer T.width (T.width / 2 - r) c ^ T.height) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusFixedChargePartitionSum_eq_sectorTrace T r hr c


-- created on 2026-10-23

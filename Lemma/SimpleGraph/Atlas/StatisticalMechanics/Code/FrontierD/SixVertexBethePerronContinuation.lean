import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
open Finset Filter Matrix Topology StatMech StatMech.FrontierD


/--
[sixVertexSectorTransferInfinity_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_apply_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexSectorTransferInfinity N n x y = if x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧ sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * n then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_apply N n x y

/--
[sixVertexSectorTransferInfinity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_nonneg_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  0 ≤ sixVertexSectorTransferInfinity N n x y := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_nonneg N n x y

/--
[sixVertexSectorTransferInfinity_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_symmetric_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexSectorTransferInfinity N n x y = sixVertexSectorTransferInfinity N n y x := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_symmetric N n x y

/--
[sixVertexSectorRowDistance_le_twice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorRowDistance_le_twice_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) ≤ 2 * n := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRowDistance_le_twice N n x y

/--
[sixVertexSectorRowDistance_eq_twice_iff_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorRowDistance_eq_twice_iff_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * n ↔ Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorRowDistance_eq_twice_iff_disjoint N n x y

/--
[tendsto_sixVertexAnisotropyPowerRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma tendsto_sixVertexAnisotropyPowerRatio_eq
  {d n : Nat}
-- given
  (hd : d ≤ 2 * n) :
-- imply
  Tendsto (fun c : Real => c ^ d / (c ^ 2 - 2) ^ n) atTop (nhds (if d = 2 * n then 1 else 0)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexAnisotropyPowerRatio hd

/--
[tendsto_sixVertexSectorTransfer_normalized_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma tendsto_sixVertexSectorTransfer_normalized_atTop_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n) :
-- imply
  Tendsto (fun c : Real => sixVertexSectorTransfer N n c x y / (c ^ 2 - 2) ^ n) atTop (nhds (sixVertexSectorTransferInfinity N n x y)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexSectorTransfer_normalized_atTop hn x y

/--
[sixVertexInfinityGraph_adj_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_noAdjacent_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hxy : (sixVertexInfinityGraph N n).Adj x y) :
-- imply
  SixVertexSectorNoAdjacent x ∧ SixVertexSectorNoAdjacent y := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_noAdjacent hxy

/--
[sixVertexNoAdjacentTransferInfinity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexNoAdjacentTransferInfinity_nonneg_eq
  {N n : Nat}
  {x y : SixVertexNoAdjacentSector N n} :
-- imply
  0 ≤ sixVertexNoAdjacentTransferInfinity N n x y := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentTransferInfinity_nonneg N n x y

/--
[sixVertexNoAdjacentTransferInfinity_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexNoAdjacentTransferInfinity_symmetric_eq
  {N n : Nat}
  {x y : SixVertexNoAdjacentSector N n} :
-- imply
  sixVertexNoAdjacentTransferInfinity N n x y = sixVertexNoAdjacentTransferInfinity N n y x := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentTransferInfinity_symmetric N n x y

/--
[sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {y : SixVertexSector N n}
-- given
  (hx : ¬ SixVertexSectorNoAdjacent x) :
-- imply
  sixVertexSectorTransferInfinity N n x y = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_left hx y

/--
[sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {y : SixVertexSector N n}
-- given
  (hy : ¬ SixVertexSectorNoAdjacent y) :
-- imply
  sixVertexSectorTransferInfinity N n x y = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_eq_zero_of_not_noAdjacent_right x hy

/--
[sixVertexNoAdjacentInfinityGraph_adjMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityGraph_adjMatrix_eq :
-- imply
  (sixVertexNoAdjacentInfinityGraph N n).adjMatrix Real = sixVertexNoAdjacentTransferInfinity N n := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityGraph_adjMatrix

/--
[sixVertexSectorPosition_alternatingEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorPosition_alternatingEven_eq
  {N n : Nat}
-- given
  (hhalf : 2 * n ≤ N) :
-- imply
  sixVertexSectorPosition (sixVertexAlternatingEvenSector N n hhalf) = sixVertexAlternatingEvenEmbedding hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_alternatingEven N n hhalf

/--
[sixVertexSectorPosition_alternatingOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorPosition_alternatingOdd_eq
  {N n : Nat}
-- given
  (hhalf : 2 * n ≤ N) :
-- imply
  sixVertexSectorPosition (sixVertexAlternatingOddSector N n hhalf) = sixVertexAlternatingOddEmbedding hhalf := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_alternatingOdd N n hhalf

/--
[sixVertexSectorPosition_alternatingEven_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorPosition_alternatingEven_apply_val_eq
  {N n : Nat}
  {k : Fin n}
-- given
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexSectorPosition (sixVertexAlternatingEvenSector N n hhalf) k).val = 2 * k.val := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_alternatingEven_apply_val N n hhalf k

/--
[sixVertexSectorPosition_alternatingOdd_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorPosition_alternatingOdd_apply_val_eq
  {N n : Nat}
  {k : Fin n}
-- given
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexSectorPosition (sixVertexAlternatingOddSector N n hhalf) k).val = 2 * k.val + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorPosition_alternatingOdd_apply_val N n hhalf k

/--
[sixVertexAlternatingEvenSector_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexAlternatingEvenSector_noAdjacent_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  SixVertexSectorNoAdjacent (sixVertexAlternatingEvenSector N n hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingEvenSector_noAdjacent hn hhalf

/--
[sixVertexAlternatingOddSector_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexAlternatingOddSector_noAdjacent_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  SixVertexSectorNoAdjacent (sixVertexAlternatingOddSector N n hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingOddSector_noAdjacent hn hhalf

/--
[sixVertexAlternatingEven_disjoint_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexAlternatingEven_disjoint_odd_eq
  {N n : Nat}
-- given
  (hhalf : 2 * n ≤ N) :
-- imply
  Disjoint ((sixVertexAlternatingEvenSector N n hhalf : SixVertexSector N n) : Finset (Fin N)) ((sixVertexAlternatingOddSector N n hhalf : SixVertexSector N n) : Finset (Fin N)) := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingEven_disjoint_odd hhalf

/--
[sixVertexInfinityGraph_adj_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_alternating_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexInfinityGraph N n).Adj (sixVertexAlternatingEvenSector N n hhalf) (sixVertexAlternatingOddSector N n hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_alternating hn hhalf

/--
[sixVertexNoAdjacentInfinityGraph_adj_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexNoAdjacentInfinityGraph_adj_alternating_eq
  {N n : Nat}
-- given
  (hn : 0 < n)
  (hhalf : 2 * n ≤ N) :
-- imply
  (sixVertexNoAdjacentInfinityGraph N n).Adj (sixVertexNoAdjacentAlternatingEven N n hn hhalf) (sixVertexNoAdjacentAlternatingOdd N n hn hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexNoAdjacentInfinityGraph_adj_alternating hn hhalf

/--
[sixVertexCyclicSuccEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexCyclicSuccEquiv_val_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  (sixVertexCyclicSuccEquiv hN i).val = (i.val + 1) % N := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicSuccEquiv_val hN i

/--
[sixVertexSector_disjoint_cyclicSucc_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSector_disjoint_cyclicSucc_of_noAdjacent_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hN : 0 < N)
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  Disjoint (x : Finset (Fin N)) ((x : Finset (Fin N)).map (sixVertexCyclicSuccEquiv hN).toEmbedding) := by
-- proof
  apply StatMech.FrontierD.sixVertexSector_disjoint_cyclicSucc_of_noAdjacent hN x hx

/--
[card_sixVertexDefectSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma card_sixVertexDefectSet_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hN : 0 < N)
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  (sixVertexDefectSet hN x).card = N - 2 * n := by
-- proof
  apply StatMech.FrontierD.card_sixVertexDefectSet hN x hx

/--
[card_sixVertexFixedChargeDefectSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma card_sixVertexFixedChargeDefectSet_eq
  {r k : Nat}
  {x : SixVertexSector (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  (sixVertexDefectSet (sixVertexFourWidth_pos r k) x).card = 2 * r := by
-- proof
  apply StatMech.FrontierD.card_sixVertexFixedChargeDefectSet r k x hx

/--
[sixVertexSectorGap_pos_of_noAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorGap_pos_of_noAdjacent_eq
  {N n : Nat}
  {x : SixVertexSector N n}
  {i : Fin n}
-- given
  (hx : SixVertexSectorNoAdjacent x) :
-- imply
  0 < sixVertexSectorGap x i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorGap_pos_of_noAdjacent x hx i

/--
[sum_sixVertexSectorGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sum_sixVertexSectorGap_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hn : 0 < n) :
-- imply
  ∑ i, sixVertexSectorGap x i = N - n := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexSectorGap x hn

/--
[sum_sixVertexSectorGapDefects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sum_sixVertexSectorGapDefects_eq
  {N n : Nat}
  {x : SixVertexSector N n}
-- given
  (hx : SixVertexSectorNoAdjacent x)
  (hn : 0 < n) :
-- imply
  ∑ i, sixVertexSectorGapDefects x i = N - 2 * n := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexSectorGapDefects x hx hn

/--
[sixVertexSectorAdvance_pos_of_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorAdvance_pos_of_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {i : Fin n}
-- given
  (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
-- imply
  0 < sixVertexSectorAdvance x y i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorAdvance_pos_of_forward_disjoint x y hforward hdisj i

/--
[sixVertexSectorAdvance_le_gap_of_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorAdvance_le_gap_of_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {i : Fin n}
-- given
  (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
-- imply
  sixVertexSectorAdvance x y i ≤ sixVertexSectorGap x i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorAdvance_le_gap_of_forward_disjoint x y hforward hdisj i

/--
[sixVertexSectorGap_transport_of_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorGap_transport_of_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {i : Fin n}
-- given
  (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
-- imply
  sixVertexSectorGap y i + sixVertexSectorAdvance x y i = sixVertexSectorGap x i + sixVertexSectorAdvance x y (sixVertexSectorCyclicNext i) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorGap_transport_of_forward_disjoint x y hforward hdisj i

/--
[sixVertexSectorGapDefects_transport_of_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorGapDefects_transport_of_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {i : Fin n}
-- given
  (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
-- imply
  sixVertexSectorGapDefects y i + sixVertexSectorAdvanceDefects x y i = sixVertexSectorGapDefects x i + sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorGapDefects_transport_of_forward_disjoint x y hforward hdisj i

/--
[sixVertexSectorAdvanceDefects_le_gapDefects_of_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorAdvanceDefects_le_gapDefects_of_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {i : Fin n}
-- given
  (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y))
  (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) :
-- imply
  sixVertexSectorAdvanceDefects x y i ≤ sixVertexSectorGapDefects x i := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorAdvanceDefects_le_gapDefects_of_forward_disjoint x y hforward hdisj i

/--
[sixVertexInfinityGraph_adj_iff_forward_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_iff_forward_disjoint_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n) :
-- imply
  (sixVertexInfinityGraph N n).Adj x y ↔ (SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧ Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) ∨ (SixVertexForwardInterlaced (sixVertexSectorRow y) (sixVertexSectorRow x) ∧ Disjoint (x : Finset (Fin N)) (y : Finset (Fin N))) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y

/--
[sixVertexInfinityGraph_adj_defect_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_defect_transport_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
-- given
  (hn : 0 < n)
  (hxy : (sixVertexInfinityGraph N n).Adj x y) :
-- imply
  (∀ i, sixVertexSectorGapDefects y i + sixVertexSectorAdvanceDefects x y i = sixVertexSectorGapDefects x i + sixVertexSectorAdvanceDefects x y (sixVertexSectorCyclicNext i)) ∨ (∀ i, sixVertexSectorGapDefects x i + sixVertexSectorAdvanceDefects y x i = sixVertexSectorGapDefects y i + sixVertexSectorAdvanceDefects y x (sixVertexSectorCyclicNext i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_defect_transport hn hxy

/--
[sixVertexInfinityGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adj_iff_eq
  {N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  (sixVertexInfinityGraph N n).Adj x y ↔ x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ∧ sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 * n := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adj_iff N n x y

/--
[sixVertexInfinityGraph_adjMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexInfinityGraph_adjMatrix_eq :
-- imply
  (sixVertexInfinityGraph N n).adjMatrix Real = sixVertexSectorTransferInfinity N n := by
-- proof
  apply StatMech.FrontierD.sixVertexInfinityGraph_adjMatrix

/--
[sixVertexSectorTransferInfinity_pow_apply_eq_card_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma sixVertexSectorTransferInfinity_pow_apply_eq_card_walk_eq
  {M N n : Nat}
  {x y : SixVertexSector N n} :
-- imply
  (sixVertexSectorTransferInfinity N n ^ M) x y = Fintype.card {w : (sixVertexInfinityGraph N n).Walk x y | w.length = M} := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTransferInfinity_pow_apply_eq_card_walk M N n x y

/--
[trace_sixVertexSectorTransferInfinity_pow_eq_closedWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma trace_sixVertexSectorTransferInfinity_pow_eq_closedWalks_eq
  {M N n : Nat} :
-- imply
  Matrix.trace (sixVertexSectorTransferInfinity N n ^ M) = ∑ x : SixVertexSector N n, (Fintype.card {w : (sixVertexInfinityGraph N n).Walk x x | w.length = M} : Real) := by
-- proof
  apply StatMech.FrontierD.trace_sixVertexSectorTransferInfinity_pow_eq_closedWalks M N n

/--
[AnalyticOnNhd.eqOn_Ioi_of_eventuallyEq_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean)
-/
@[path]
private lemma eqOn_Ioi_of_eventuallyEq_atTop_eq
  {f g : Real → Real}
  {a : Real}
-- given
  (hf : AnalyticOnNhd Real f (Set.Ioi a))
  (hg : AnalyticOnNhd Real g (Set.Ioi a))
  (hfg : f =ᶠ[atTop] g) :
-- imply
  Set.EqOn f g (Set.Ioi a) := by
-- proof
  apply StatMech.FrontierD.AnalyticOnNhd.eqOn_Ioi_of_eventuallyEq_atTop hf hg hfg


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
open Set SimpleGraph Finset MeasureTheory StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc57_offAxisLine_no_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_offAxisLine_no_reachesNbr_eq :
-- imply
  ¬ bc56_ClusterReachesNbr bc56_offAxisLine (bc56_lp 0) := by
-- proof
  apply StatMech.Walls.bc57_offAxisLine_no_reachesNbr

/--
[bc57_pt_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_fst_eq
-- given
  (k h : ℤ) :
-- imply
  (bc57_pt k h) 0 = k := by
-- proof
  apply StatMech.Walls.bc57_pt_fst k h

/--
[bc57_pt_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_snd_eq
-- given
  (k h : ℤ) :
-- imply
  (bc57_pt k h) 1 = h := by
-- proof
  apply StatMech.Walls.bc57_pt_snd k h

/--
[bc57_pt_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_inj_eq
  {k k' h h' : ℤ}
-- given
  (hk : k = k')
  (hh : h = h') :
-- imply
  bc57_pt k h = bc57_pt k' h' := by
-- proof
  apply StatMech.Walls.bc57_pt_inj hk hh

/--
[bc57_pt_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_adj_eq
-- given
  (k h : ℤ) :
-- imply
  (hypercubicLattice 2).Adj (bc57_pt k h) (bc57_pt (k + 1) h) := by
-- proof
  apply StatMech.Walls.bc57_pt_adj k h

/--
[bc57_evenLines_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_evenLines_open_eq
  {k m : ℤ} :
-- imply
  bc57_evenLines s(bc57_pt k (2 * m), bc57_pt (k + 1) (2 * m)) = true := by
-- proof
  apply StatMech.Walls.bc57_evenLines_open k m

/--
[bc57_connected_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_connected_pos_eq
  {m : ℤ}
  {j : ℕ} :
-- imply
  Connected 2 bc57_evenLines (bc57_pt 0 (2 * m)) (bc57_pt (j : ℤ) (2 * m)) := by
-- proof
  apply StatMech.Walls.bc57_connected_pos m j

/--
[bc57_height_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_height_step_eq
  {h : ℤ}
  {u v : Site 2}
-- given
  (hu : u 1 = h)
  (hadj : (openSubgraph 2 bc57_evenLines).Adj u v) :
-- imply
  v 1 = h := by
-- proof
  apply StatMech.Walls.bc57_height_step hu hadj

/--
[bc57_height_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_height_invariant_eq
  {h : ℤ}
  {u y : Site 2}
-- given
  (hu : u 1 = h)
  (hconn : Connected 2 bc57_evenLines u y) :
-- imply
  y 1 = h := by
-- proof
  apply StatMech.Walls.bc57_height_invariant hu hconn

/--
[bc57_pt_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_outside_box_eq
  {j : ℕ}
  {m : ℤ} :
-- imply
  bc57_pt ((j : ℤ) + 1) (2 * m) ∉ box 2 j := by
-- proof
  apply StatMech.Walls.bc57_pt_outside_box j m

/--
[bc57_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_cluster_infinite_eq
  {m : ℤ} :
-- imply
  (cluster 2 bc57_evenLines (bc57_pt 0 (2 * m))).Infinite := by
-- proof
  apply StatMech.Walls.bc57_cluster_infinite m

/--
[bc57_pt_zero_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_pt_zero_mem_box_eq
  {m : ℤ}
  {n : ℕ}
-- given
  (hm : (2 * m).natAbs ≤ n) :
-- imply
  bc57_pt 0 (2 * m) ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bc57_pt_zero_mem_box hm

/--
[bc57_cluster_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_cluster_ne_eq
  {m m' : ℤ}
-- given
  (h : m ≠ m') :
-- imply
  cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)) ≠ cluster 2 bc57_evenLines (bc57_pt 0 (2 * m')) := by
-- proof
  apply StatMech.Walls.bc57_cluster_ne h

/--
[bc57_cluster_family_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_cluster_family_inj_eq :
-- imply
  Function.Injective (fun m : ℤ => cluster 2 bc57_evenLines (bc57_pt 0 (2 * m))) := by
-- proof
  apply StatMech.Walls.bc57_cluster_family_inj

/--
[bc57_numInfiniteClusters_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_numInfiniteClusters_top_eq :
-- imply
  numInfiniteClusters 2 bc57_evenLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc57_numInfiniteClusters_top

/--
[bc57_no_originNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_no_originNbr_eq
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ∀ a : Site 2, (hypercubicLattice 2).Adj 0 a → a ∉ cluster 2 bc57_evenLines (bc57_pt 0 (2 * m)) := by
-- proof
  apply StatMech.Walls.bc57_no_originNbr hm

/--
[bc57_no_reachesNbr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_no_reachesNbr_eq
  {m : ℤ}
-- given
  (hm : m ≠ 0) :
-- imply
  ¬ bc56_ClusterReachesNbr bc57_evenLines (bc57_pt 0 (2 * m)) := by
-- proof
  apply StatMech.Walls.bc57_no_reachesNbr hm

/--
[bc57_mem_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_mem_threeMeetBox_eq :
-- imply
  bc57_evenLines ∈ threeMeetBox 2 6 := by
-- proof
  apply StatMech.Walls.bc57_mem_threeMeetBox

/--
[bc57_boxClusterReachesNbr_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_boxClusterReachesNbr_false_eq :
-- imply
  ¬ bc56_BoxClusterReachesNbr 2 6 := by
-- proof
  apply StatMech.Walls.bc57_boxClusterReachesNbr_false

/--
[bc57_boxMengerAttachment_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_boxMengerAttachment_false_eq :
-- imply
  ¬ bmm_BoxMengerAttachment 2 6 := by
-- proof
  apply StatMech.Walls.bc57_boxMengerAttachment_false

/--
[bc57_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc57coarsetrif.lean)
-/
@[path]
private lemma bc57_status_eq :
-- imply
  (¬ bc56_BoxClusterReachesNbr 2 6) ∧ (¬ bmm_BoxMengerAttachment 2 6) ∧ (bc57_evenLines ∈ threeMeetBox 2 6) ∧ (numInfiniteClusters 2 bc57_evenLines = ⊤) ∧ (∀ m : ℤ, m ≠ 0 → ¬ bc56_ClusterReachesNbr bc57_evenLines (bc57_pt 0 (2 * m))) := by
-- proof
  apply StatMech.Walls.bc57_status


-- created on 2026-10-23

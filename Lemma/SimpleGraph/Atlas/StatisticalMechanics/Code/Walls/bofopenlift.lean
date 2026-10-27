import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bofopenlift
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bof_ce_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_ce_true_iff_eq
  {e : Sym2 (Site 2)} :
-- imply
  bof_ce e = true ↔ ((∃ k : ℤ, e = s(bc57_pt k 0, bc57_pt (k + 1) 0)) ∨ (∃ k : ℤ, e = s(bc57_pt k 2, bc57_pt (k + 1) 2)) ∨ (e = s(bc57_pt 0 0, bc57_pt 0 1)) ∨ (e = s(bc57_pt 0 1, bc57_pt 0 2))) := by
-- proof
  apply StatMech.Walls.bof_ce_true_iff e

/--
[bof_horiz0_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_horiz0_open_eq
  {k : ℤ} :
-- imply
  bof_ce s(bc57_pt k 0, bc57_pt (k + 1) 0) = true := by
-- proof
  apply StatMech.Walls.bof_horiz0_open k

/--
[bof_horiz2_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_horiz2_open_eq
  {k : ℤ} :
-- imply
  bof_ce s(bc57_pt k 2, bc57_pt (k + 1) 2) = true := by
-- proof
  apply StatMech.Walls.bof_horiz2_open k

/--
[bof_bridge1_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_bridge1_open_eq :
-- imply
  bof_ce s(bc57_pt 0 0, bc57_pt 0 1) = true := by
-- proof
  apply StatMech.Walls.bof_bridge1_open

/--
[bof_bridge2_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_bridge2_open_eq :
-- imply
  bof_ce s(bc57_pt 0 1, bc57_pt 0 2) = true := by
-- proof
  apply StatMech.Walls.bof_bridge2_open

/--
[bof_box_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_box_mem_eq
  {x : Site 2} :
-- imply
  x ∈ bc61_boxAround 2 0 (bc57_pt 0 1) ↔ x = bc57_pt 0 1 := by
-- proof
  apply StatMech.Walls.bof_box_mem x

/--
[bof_line0_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_line0_notMem_eq
  {k : ℤ} :
-- imply
  bc57_pt k 0 ∉ bc61_boxAround 2 0 (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bof_line0_notMem k

/--
[bof_line2_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_line2_notMem_eq
  {k : ℤ} :
-- imply
  bc57_pt k 2 ∉ bc61_boxAround 2 0 (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bof_line2_notMem k

/--
[bof_rm_height_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_height_step_eq
  {h : ℤ}
  {u v : Site 2}
-- given
  (hu : u 1 = h)
  (hadj : (openSubgraph 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce)).Adj u v) :
-- imply
  v 1 = h := by
-- proof
  apply StatMech.Walls.bof_rm_height_step hu hadj

/--
[bof_rm_height_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_height_inv_eq
  {h : ℤ}
  {u y : Site 2}
-- given
  (hu : u 1 = h)
  (hconn : Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) u y) :
-- imply
  y 1 = h := by
-- proof
  apply StatMech.Walls.bof_rm_height_inv hu hconn

/--
[bof_rm_line0_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_line0_step_eq
  {k : ℤ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt k 0) (bc57_pt (k + 1) 0) := by
-- proof
  apply StatMech.Walls.bof_rm_line0_step k

/--
[bof_rm_line2_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_line2_step_eq
  {k : ℤ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt k 2) (bc57_pt (k + 1) 2) := by
-- proof
  apply StatMech.Walls.bof_rm_line2_step k

/--
[bof_rm_line0_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_line0_reach_eq
  {j : ℕ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 0) (bc57_pt ((5 : ℤ) + (j : ℤ)) 0) := by
-- proof
  apply StatMech.Walls.bof_rm_line0_reach j

/--
[bof_rm_line2_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_rm_line2_reach_eq
  {j : ℕ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 2) (bc57_pt ((5 : ℤ) + (j : ℤ)) 2) := by
-- proof
  apply StatMech.Walls.bof_rm_line2_reach j

/--
[bof_cluster_u_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_cluster_u_infinite_eq :
-- imply
  (cluster 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 0)).Infinite := by
-- proof
  apply StatMech.Walls.bof_cluster_u_infinite

/--
[bof_cluster_v_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_cluster_v_infinite_eq :
-- imply
  (cluster 2 (removeSites (bc61_boxAround 2 0 (bc57_pt 0 1)) bof_ce) (bc57_pt 5 2)).Infinite := by
-- proof
  apply StatMech.Walls.bof_cluster_v_infinite

/--
[bof_line0_from0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_line0_from0_eq
  {n : ℤ} :
-- imply
  Connected 2 bof_ce (bc57_pt 0 0) (bc57_pt n 0) := by
-- proof
  apply StatMech.Walls.bof_line0_from0 n

/--
[bof_line2_from0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_line2_from0_eq
  {n : ℤ} :
-- imply
  Connected 2 bof_ce (bc57_pt 0 2) (bc57_pt n 2) := by
-- proof
  apply StatMech.Walls.bof_line2_from0 n

/--
[bof_uv_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_uv_connected_eq :
-- imply
  (openSubgraph 2 bof_ce).Reachable (bc57_pt 5 0) (bc57_pt 5 2) := by
-- proof
  apply StatMech.Walls.bof_uv_connected

/--
[bof_not_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_not_reconnect_eq :
-- imply
  ¬ (bc67_contractedLattice bof_ce 0 (bc57_pt 0 1)).Reachable (bc57_pt 5 0) (bc57_pt 5 2) := by
-- proof
  apply StatMech.Walls.bof_not_reconnect

/--
[bof_ClusterReconnect_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_ClusterReconnect_false_eq :
-- imply
  ¬ ben_ClusterReconnect bof_ce 0 (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bof_ClusterReconnect_false

/--
[bof_residue_not_universal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_residue_not_universal_eq :
-- imply
  ∃ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (tipj : Site 2), ¬ ben_ClusterReconnect ω L tipj := by
-- proof
  apply StatMech.Walls.bof_residue_not_universal

/--
[bof_openLift_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bofopenlift.lean)
-/
@[path]
private lemma bof_openLift_fails_eq :
-- imply
  (∃ (hu : (bc57_pt 5 0) ∉ (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2))) (hv : (bc57_pt 5 2) ∉ (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2))), ((hypercubicLattice 2).induce (↑(bc61_boxAround 2 0 (bc57_pt 0 1)) : Set (Site 2))ᶜ).Reachable ⟨bc57_pt 5 0, hu⟩ ⟨bc57_pt 5 2, hv⟩) ∧ ¬ (bc67_contractedLattice bof_ce 0 (bc57_pt 0 1)).Reachable (bc57_pt 5 0) (bc57_pt 5 2) := by
-- proof
  apply StatMech.Walls.bof_openLift_fails


-- created on 2026-10-23

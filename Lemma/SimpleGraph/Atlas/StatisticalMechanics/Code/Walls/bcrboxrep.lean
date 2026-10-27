import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bcrboxrep.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bcr_path_crosses_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_path_crosses_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
  {u v : Site d}
  {p : (openSubgraph d ω).Walk u v}
-- given
  (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
-- imply
  ∃ w ∈ p.support, w ∈ bc61_boxAround d L x := by
-- proof
  apply StatMech.Walls.bcr_path_crosses_box ω L x p hcut

/--
[bcr_boxRep_of_fullConn_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_boxRep_of_fullConn_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
  {u v : Site d}
-- given
  (hconn : (openSubgraph d ω).Reachable u v)
  (hcut : ¬ (bc67_contractedLattice ω L x).Reachable u v) :
-- imply
  ∃ r ∈ bc61_boxAround d L x, (openSubgraph d ω).Reachable u r ∧ (openSubgraph d ω).Reachable r v := by
-- proof
  apply StatMech.Walls.bcr_boxRep_of_fullConn_cut ω L x hconn hcut

/--
[bcr_center_reaches_arm_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_center_reaches_arm_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hgen : btr_IsGenuineCoarseTrif ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (openSubgraph d ω).Reachable y a₁ ∧ (openSubgraph d ω).Reachable y a₂ ∧ (openSubgraph d ω).Reachable y a₃ := by
-- proof
  apply StatMech.Walls.bcr_center_reaches_arm_full ω L hgen

/--
[bcr_connectedRep_of_genuineCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_connectedRep_of_genuineCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hgen : btr_IsGenuineCoarseTrif ω L y) :
-- imply
  ∃ (r : Site d) (a₁ a₂ a₃ : Site d), r ∈ bc61_boxAround d L y ∧ (openSubgraph d ω).Reachable r y ∧ (openSubgraph d ω).Reachable r a₁ ∧ (openSubgraph d ω).Reachable r a₂ ∧ (openSubgraph d ω).Reachable r a₃ := by
-- proof
  apply StatMech.Walls.bcr_connectedRep_of_genuineCluster ω L hgen

/--
[bcr_upperLines_not_genuineCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_upperLines_not_genuineCluster_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2} :
-- imply
  ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y := by
-- proof
  apply StatMech.Walls.bcr_upperLines_not_genuineCluster L y

/--
[bcr_upperLines_no_connectedRep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_upperLines_no_connectedRep_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2} :
-- imply
  ¬ ∃ (_hgen : btr_IsGenuineCoarseTrif bc60_upperLines L y) (r : Site 2) (a₁ a₂ a₃ : Site 2), r ∈ bc61_boxAround 2 L y ∧ (openSubgraph 2 bc60_upperLines).Reachable r y ∧ (openSubgraph 2 bc60_upperLines).Reachable r a₁ ∧ (openSubgraph 2 bc60_upperLines).Reachable r a₂ ∧ (openSubgraph 2 bc60_upperLines).Reachable r a₃ := by
-- proof
  apply StatMech.Walls.bcr_upperLines_no_connectedRep L y

/--
[bcr_hroute_via_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_hroute_via_branch_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {aj x b tip : Site d}
-- given
  (hxb : (bc67_contractedLattice ω L aj).Reachable x b)
  (hbt : (bc67_contractedLattice ω L aj).Reachable b tip) :
-- imply
  (bc67_contractedLattice ω L aj).Reachable x tip := by
-- proof
  apply StatMech.Walls.bcr_hroute_via_branch ω L aj x b tip hxb hbt

/--
[bcr_center_reaches_branch_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_center_reaches_branch_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y arm b : Site d}
-- given
  (hcy : (openSubgraph d ω).Reachable y arm)
  (hab : (bc67_contractedLattice ω L y).Reachable arm b) :
-- imply
  (openSubgraph d ω).Reachable y b := by
-- proof
  apply StatMech.Walls.bcr_center_reaches_branch_full ω L hcy hab

/--
[bcr_cross_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cross_horiz_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  bcr_cross s(bc57_pt k 0, bc57_pt (k + 1) 0) = true := by
-- proof
  apply StatMech.Walls.bcr_cross_horiz k

/--
[bcr_cross_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cross_vert_eq
  {d : ℕ}
-- given
  (h : ℤ) :
-- imply
  bcr_cross s(bc57_pt 0 h, bc57_pt 0 (h + 1)) = true := by
-- proof
  apply StatMech.Walls.bcr_cross_vert h

/--
[bcr_vert_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_vert_adj_eq
  {d : ℕ}
-- given
  (h : ℤ) :
-- imply
  (hypercubicLattice 2).Adj (bc57_pt 0 h) (bc57_pt 0 (h + 1)) := by
-- proof
  apply StatMech.Walls.bcr_vert_adj h

/--
[bcr_cross_open_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cross_open_coord_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (h : bcr_cross s(u, v) = true) :
-- imply
  (u 1 = 0 ∧ v 1 = 0) ∨ (u 0 = 0 ∧ v 0 = 0) := by
-- proof
  apply StatMech.Walls.bcr_cross_open_coord h

/--
[bcr_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_out_eq
  {d : ℕ}
  {L : ℕ}
  {C H : ℤ}
-- given
  (h : L < C.natAbs ∨ L < H.natAbs) :
-- imply
  bc57_pt C H ∉ bc61_boxAround 2 L (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bcr_out h

/--
[bcr_hreach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_hreach_eq
  {d : ℕ}
  {c : ℤ}
  {j : ℕ} :
-- imply
  Connected 2 bcr_cross (bc57_pt c 0) (bc57_pt (c + (j : ℤ)) 0) := by
-- proof
  apply StatMech.Walls.bcr_hreach c j

/--
[bcr_vreach_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_vreach_up_eq
  {d : ℕ}
  {j : ℕ}
-- given
  (hgt : ℤ) :
-- imply
  Connected 2 bcr_cross (bc57_pt 0 hgt) (bc57_pt 0 (hgt + (j : ℤ))) := by
-- proof
  apply StatMech.Walls.bcr_vreach_up hgt j

/--
[bcr_vreach_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_vreach_down_eq
  {d : ℕ}
  {j : ℕ}
-- given
  (hgt : ℤ) :
-- imply
  Connected 2 bcr_cross (bc57_pt 0 hgt) (bc57_pt 0 (hgt - (j : ℤ))) := by
-- proof
  apply StatMech.Walls.bcr_vreach_down hgt j

/--
[bcr_cut_hreach_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cut_hreach_pos_eq
  {d : ℕ}
  {L : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) (bc57_pt ((L : ℤ) + 1) 0) (bc57_pt ((L : ℤ) + 1 + (j : ℤ)) 0) := by
-- proof
  apply StatMech.Walls.bcr_cut_hreach_pos L j

/--
[bcr_cut_vreach_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cut_vreach_up_eq
  {d : ℕ}
  {L : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) (bc57_pt 0 ((L : ℤ) + 1)) (bc57_pt 0 ((L : ℤ) + 1 + (j : ℤ))) := by
-- proof
  apply StatMech.Walls.bcr_cut_vreach_up L j

/--
[bcr_cut_vreach_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cut_vreach_down_eq
  {d : ℕ}
  {L : ℕ}
  {j : ℕ} :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) (bc57_pt 0 (-(L : ℤ) - 1)) (bc57_pt 0 (-(L : ℤ) - 1 - (j : ℤ))) := by
-- proof
  apply StatMech.Walls.bcr_cut_vreach_down L j

/--
[bcr_inv_flat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_inv_flat_eq
  {d : ℕ}
  {L : ℕ}
  {u v : Site 2}
-- given
  (hconn : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) u v)
  (hu : u 1 = 0 ∧ u 0 ≠ 0) :
-- imply
  v 1 = 0 ∧ v 0 ≠ 0 := by
-- proof
  apply StatMech.Walls.bcr_inv_flat L hconn hu

/--
[bcr_inv_plusy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_inv_plusy_eq
  {d : ℕ}
  {L : ℕ}
  {u v : Site 2}
-- given
  (hconn : Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt 0 0)) bcr_cross) u v)
  (hu : u 0 = 0 ∧ (L : ℤ) < u 1) :
-- imply
  v 0 = 0 ∧ (L : ℤ) < v 1 := by
-- proof
  apply StatMech.Walls.bcr_inv_plusy L hconn hu

/--
[bcr_cross_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cross_genuineTrif_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  btr_IsGenuineCoarseTrif bcr_cross L (bc57_pt 0 0) := by
-- proof
  apply StatMech.Walls.bcr_cross_genuineTrif L

/--
[bcr_cross_rep_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_cross_rep_fires_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  ∃ (r : Site 2) (a₁ a₂ a₃ : Site 2), r ∈ bc61_boxAround 2 L (bc57_pt 0 0) ∧ (openSubgraph 2 bcr_cross).Reachable r (bc57_pt 0 0) ∧ (openSubgraph 2 bcr_cross).Reachable r a₁ ∧ (openSubgraph 2 bcr_cross).Reachable r a₂ ∧ (openSubgraph 2 bcr_cross).Reachable r a₃ := by
-- proof
  apply StatMech.Walls.bcr_cross_rep_fires L

/--
[bcr_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcrboxrep.lean)
-/
@[path]
private lemma bcr_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x u v : Site d) (p : (openSubgraph d ω).Walk u v), ¬ (bc67_contractedLattice ω L x).Reachable u v → ∃ w ∈ p.support, w ∈ bc61_boxAround d L x) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), btr_IsGenuineCoarseTrif ω L y → ∃ (r : Site d) (a₁ a₂ a₃ : Site d), r ∈ bc61_boxAround d L y ∧ (openSubgraph d ω).Reachable r y ∧ (openSubgraph d ω).Reachable r a₁ ∧ (openSubgraph d ω).Reachable r a₂ ∧ (openSubgraph d ω).Reachable r a₃) ∧ (∀ (L : ℕ) (y : Site 2), ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y arm b : Site d), (openSubgraph d ω).Reachable y arm → (bc67_contractedLattice ω L y).Reachable arm b → (openSubgraph d ω).Reachable y b) := by
-- proof
  apply StatMech.Walls.bcr_status


-- created on 2026-10-23

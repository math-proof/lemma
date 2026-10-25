import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc60upperlines.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc60_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_open_eq
  {k : ℤ}
  {h : ℤ}
-- given
  (hh : 1 ≤ h) :
-- imply
  bc60_upperLines s(bc57_pt k h, bc57_pt (k + 1) h) = true := by
-- proof
  apply StatMech.Walls.bc60_open k hh

/--
[bc60_removeSite_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_removeSite_mono_eq
  {G : Finset (Sym2 (Site 2))} :
-- imply
  removeSite 0 bc60_upperLines ≤ removeSite 0 (forceOpenFinset G bc60_upperLines) := by
-- proof
  apply StatMech.Walls.bc60_removeSite_mono G

/--
[bc60_connected_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_connected_forceOpen_eq
  {G : Finset (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (h : Connected 2 (removeSite 0 bc60_upperLines) x y) :
-- imply
  Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) x y := by
-- proof
  apply StatMech.Walls.bc60_connected_forceOpen h

/--
[bc60_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_origin_eq_eq :
-- imply
  (0 : Site 2) = bc57_pt 0 0 := by
-- proof
  apply StatMech.Walls.bc60_origin_eq

/--
[bc60_pt_eq_origin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_pt_eq_origin_iff_eq
  {a b : ℤ} :
-- imply
  bc57_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
-- proof
  apply StatMech.Walls.bc60_pt_eq_origin_iff

/--
[bc60_open_edge_heights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_open_edge_heights_eq
  {u v : Site 2}
-- given
  (hopen : bc60_upperLines s(u, v) = true) :
-- imply
  1 ≤ u 1 ∧ 1 ≤ v 1 ∧ u 1 = v 1 := by
-- proof
  apply StatMech.Walls.bc60_open_edge_heights hopen

/--
[bc60_line1_reach_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_line1_reach_pos_eq
  {j : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (j : ℤ) 1) := by
-- proof
  apply StatMech.Walls.bc60_line1_reach_pos j

/--
[bc60_line1_reach_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_line1_reach_neg_eq
  {j : ℕ} :
-- imply
  Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (-(j : ℤ)) 1) := by
-- proof
  apply StatMech.Walls.bc60_line1_reach_neg j

/--
[bc60_line1_connected_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_line1_connected_zero_eq
  {m : ℤ} :
-- imply
  Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bc60_line1_connected_zero m

/--
[bc60_line1_all_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_line1_all_connected_eq
  {m m' : ℤ} :
-- imply
  Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt m' 1) := by
-- proof
  apply StatMech.Walls.bc60_line1_all_connected m m'

/--
[bc60_step_height_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_step_height_diff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {u v : Site 2}
-- given
  (hadj : (openSubgraph 2 ω).Adj u v) :
-- imply
  (u 1 - v 1).natAbs ≤ 1 := by
-- proof
  apply StatMech.Walls.bc60_step_height_diff hadj

/--
[bc60_reach_height_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_reach_height_one_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {u y : Site 2}
-- given
  (hu : u 1 ≤ 0)
  (hy : 1 ≤ y 1)
  (hconn : Connected 2 ω u y) :
-- imply
  ∃ w : Site 2, w 1 = 1 ∧ Connected 2 ω u w := by
-- proof
  apply StatMech.Walls.bc60_reach_height_one hu hy hconn

/--
[bc60_mem_Gverts_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_mem_Gverts_left_eq
  {G : Finset (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (h : s(x, y) ∈ G) :
-- imply
  x ∈ bc60_Gverts G := by
-- proof
  apply StatMech.Walls.bc60_mem_Gverts_left h

/--
[bc60_mem_Gverts_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_mem_Gverts_right_eq
  {G : Finset (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (h : s(x, y) ∈ G) :
-- imply
  y ∈ bc60_Gverts G := by
-- proof
  apply StatMech.Walls.bc60_mem_Gverts_right h

/--
[bc60_confined_mem_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_confined_mem_insert_eq
  {G : Finset (Sym2 (Site 2))}
  {p y : Site 2}
  {w : (openSubgraph 2 (removeSite 0 (forceOpenFinset G bc60_upperLines))).Walk p y}
-- given
  (hlow : ∀ z, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) p z → z 1 ≤ 0) :
-- imply
  y ∈ insert p (bc60_Gverts G) := by
-- proof
  apply StatMech.Walls.bc60_confined_mem_insert hlow w

/--
[bc60_arm_reaches_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_arm_reaches_up_eq
  {G : Finset (Sym2 (Site 2))}
  {a : Site 2}
-- given
  (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite) :
-- imply
  ∃ w : Site 2, 1 ≤ w 1 ∧ Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a w := by
-- proof
  apply StatMech.Walls.bc60_arm_reaches_up hinf

/--
[bc60_pt_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_pt_coord_eq
  {v : Site 2} :
-- imply
  v = bc57_pt (v 0) (v 1) := by
-- proof
  apply StatMech.Walls.bc60_pt_coord v

/--
[bc60_arm_reaches_line1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_arm_reaches_line1_eq
  {G : Finset (Sym2 (Site 2))}
  {a : Site 2}
-- given
  (ha : a 1 ≤ 1)
  (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite) :
-- imply
  ∃ m : ℤ, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a (bc57_pt m 1) := by
-- proof
  apply StatMech.Walls.bc60_arm_reaches_line1 ha hinf

/--
[bc60_arms_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_arms_connected_eq
  {G : Finset (Sym2 (Site 2))}
  {a a' : Site 2}
-- given
  (ha : a 1 ≤ 1)
  (ha' : a' 1 ≤ 1)
  (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
  (hinf' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
-- imply
  Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' := by
-- proof
  apply StatMech.Walls.bc60_arms_connected ha ha' hinf hinf'

/--
[bc60_line_reach_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_line_reach_pos_eq
  {h : ℤ}
  {j : ℕ}
-- given
  (hh : 1 ≤ h) :
-- imply
  Connected 2 bc60_upperLines (bc57_pt 0 h) (bc57_pt (j : ℤ) h) := by
-- proof
  apply StatMech.Walls.bc60_line_reach_pos hh j

/--
[bc60_pt_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_pt_outside_box_eq
  {j : ℕ}
-- given
  (h : ℤ) :
-- imply
  bc57_pt ((j : ℤ) + 1) h ∉ box 2 j := by
-- proof
  apply StatMech.Walls.bc60_pt_outside_box j h

/--
[bc60_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_cluster_infinite_eq
  {h : ℤ}
-- given
  (hh : 1 ≤ h) :
-- imply
  (cluster 2 bc60_upperLines (bc57_pt 0 h)).Infinite := by
-- proof
  apply StatMech.Walls.bc60_cluster_infinite hh

/--
[bc60_pt_zero_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_pt_zero_mem_box_eq
  {h : ℤ}
  {n : ℕ}
-- given
  (hh : h.natAbs ≤ n) :
-- imply
  bc57_pt 0 h ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bc60_pt_zero_mem_box hh

/--
[bc60_height_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_height_invariant_eq
  {h : ℤ}
  {u y : Site 2}
-- given
  (hu : u 1 = h)
  (hconn : Connected 2 bc60_upperLines u y) :
-- imply
  y 1 = h := by
-- proof
  apply StatMech.Walls.bc60_height_invariant hu hconn

/--
[bc60_cluster_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_cluster_ne_eq
  {h h' : ℤ}
-- given
  (hne : h ≠ h') :
-- imply
  cluster 2 bc60_upperLines (bc57_pt 0 h) ≠ cluster 2 bc60_upperLines (bc57_pt 0 h') := by
-- proof
  apply StatMech.Walls.bc60_cluster_ne hne

/--
[bc60_cluster_family_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_cluster_family_inj_eq :
-- imply
  Function.Injective (fun n : ℕ => cluster 2 bc60_upperLines (bc57_pt 0 ((n : ℤ) + 1))) := by
-- proof
  apply StatMech.Walls.bc60_cluster_family_inj

/--
[bc60_numInfiniteClusters_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_numInfiniteClusters_top_eq :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc60_numInfiniteClusters_top

/--
[bc60_mem_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_mem_threeMeetBox_eq :
-- imply
  bc60_upperLines ∈ threeMeetBox 2 3 := by
-- proof
  apply StatMech.Walls.bc60_mem_threeMeetBox

/--
[bc60_nbr_height_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_nbr_height_le_eq
  {a : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj 0 a) :
-- imply
  a 1 ≤ 1 := by
-- proof
  apply StatMech.Walls.bc60_nbr_height_le hadj

/--
[bc60_not_disjointCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_not_disjointCorridors_eq :
-- imply
  ¬ bc59_DisjointCorridors bc60_upperLines := by
-- proof
  apply StatMech.Walls.bc60_not_disjointCorridors

/--
[bc60_not_hasDisjointCorridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_not_hasDisjointCorridors_eq :
-- imply
  ¬ bc59_HasDisjointCorridors 2 3 := by
-- proof
  apply StatMech.Walls.bc60_not_hasDisjointCorridors

/--
[bc60_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean)
-/
@[path]
private lemma bc60_status_eq :
-- imply
  (bc60_upperLines ∈ threeMeetBox 2 3) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) ∧ (¬ bc59_DisjointCorridors bc60_upperLines) ∧ (¬ bc59_HasDisjointCorridors 2 3) := by
-- proof
  apply StatMech.Walls.bc60_status


-- created on 2026-10-23

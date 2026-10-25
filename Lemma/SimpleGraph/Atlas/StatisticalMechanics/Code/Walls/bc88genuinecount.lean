import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc88genuinecount
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc88_genuine_count_le_boundary_of_openForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_genuine_count_le_boundary_of_openForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc88_genuine_count_le_boundary_of_openForest ω n h

/--
[bc88_branch_le_leaf_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_branch_le_leaf_unconditional_eq
  {d : ℕ}
  [Fintype W]
  [Nonempty W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc88_branch_le_leaf_unconditional G hacyc hmin

/--
[bc88_left_ray_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_left_ray_step_eq
  {d : ℕ}
  {a b : Site 2}
-- given
  (hab : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Adj a b)
  (ha : a 1 = 1 ∧ a 0 ≤ -1) :
-- imply
  b 1 = 1 ∧ b 0 ≤ -1 := by
-- proof
  apply StatMech.Walls.bc88_left_ray_step hab ha

/--
[bc88_left_ray_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_left_ray_invariant_eq
  {d : ℕ}
  {y : Site 2}
-- given
  (hconn : Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt (-1) 1) y) :
-- imply
  y 1 = 1 ∧ y 0 ≤ -1 := by
-- proof
  apply StatMech.Walls.bc88_left_ray_invariant hconn

/--
[bc88_right_ray_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_right_ray_step_eq
  {d : ℕ}
  {a b : Site 2}
-- given
  (hab : (openSubgraph 2 (removeSite (bc57_pt 0 1) bc60_upperLines)).Adj a b)
  (ha : a 1 = 1 ∧ 1 ≤ a 0) :
-- imply
  b 1 = 1 ∧ 1 ≤ b 0 := by
-- proof
  apply StatMech.Walls.bc88_right_ray_step hab ha

/--
[bc88_right_ray_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_right_ray_invariant_eq
  {d : ℕ}
  {y : Site 2}
-- given
  (hconn : Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 1 1) y) :
-- imply
  y 1 = 1 ∧ 1 ≤ y 0 := by
-- proof
  apply StatMech.Walls.bc88_right_ray_invariant hconn

/--
[bc88_left_right_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_left_right_disconnected_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt (-1) 1) (bc57_pt 1 1) := by
-- proof
  apply StatMech.Walls.bc88_left_right_disconnected

/--
[bc88_center_left_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_center_left_disconnected_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 0 1) (bc57_pt (-1) 1) := by
-- proof
  apply StatMech.Walls.bc88_center_left_disconnected

/--
[bc88_center_right_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_center_right_disconnected_eq
  {d : ℕ} :
-- imply
  ¬ Connected 2 (removeSite (bc57_pt 0 1) bc60_upperLines) (bc57_pt 0 1) (bc57_pt 1 1) := by
-- proof
  apply StatMech.Walls.bc88_center_right_disconnected

/--
[bc88_line_pts_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_line_pts_infinite_eq
  {d : ℕ}
  {m : ℤ} :
-- imply
  (cluster 2 bc60_upperLines (bc57_pt m 1)).Infinite := by
-- proof
  apply StatMech.Walls.bc88_line_pts_infinite m

/--
[bc88_upperLines_isTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_upperLines_isTrifurcation_eq
  {d : ℕ} :
-- imply
  IsTrifurcation 2 bc60_upperLines (bc57_pt 0 1) := by
-- proof
  apply StatMech.Walls.bc88_upperLines_isTrifurcation

/--
[bc88_left_ray_step_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_left_ray_step_gen_eq
  {d : ℕ}
  {c : ℤ}
  {a b : Site 2}
-- given
  (hab : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Adj a b)
  (ha : a 1 = 1 ∧ a 0 ≤ c - 1) :
-- imply
  b 1 = 1 ∧ b 0 ≤ c - 1 := by
-- proof
  apply StatMech.Walls.bc88_left_ray_step_gen hab ha

/--
[bc88_right_ray_step_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_right_ray_step_gen_eq
  {d : ℕ}
  {c : ℤ}
  {a b : Site 2}
-- given
  (hab : (openSubgraph 2 (removeSite (bc57_pt c 1) bc60_upperLines)).Adj a b)
  (ha : a 1 = 1 ∧ c + 1 ≤ a 0) :
-- imply
  b 1 = 1 ∧ c + 1 ≤ b 0 := by
-- proof
  apply StatMech.Walls.bc88_right_ray_step_gen hab ha

/--
[bc88_left_ray_invariant_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_left_ray_invariant_gen_eq
  {d : ℕ}
  {c : ℤ}
  {y : Site 2}
-- given
  (hconn : Connected 2 (removeSite (bc57_pt c 1) bc60_upperLines) (bc57_pt (c - 1) 1) y) :
-- imply
  y 1 = 1 ∧ y 0 ≤ c - 1 := by
-- proof
  apply StatMech.Walls.bc88_left_ray_invariant_gen hconn

/--
[bc88_right_ray_invariant_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_right_ray_invariant_gen_eq
  {d : ℕ}
  {c : ℤ}
  {y : Site 2}
-- given
  (hconn : Connected 2 (removeSite (bc57_pt c 1) bc60_upperLines) (bc57_pt (c + 1) 1) y) :
-- imply
  y 1 = 1 ∧ c + 1 ≤ y 0 := by
-- proof
  apply StatMech.Walls.bc88_right_ray_invariant_gen hconn

/--
[bc88_upperLines_isTrifurcation_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_upperLines_isTrifurcation_general_eq
  {d : ℕ}
  {k : ℤ} :
-- imply
  IsTrifurcation 2 bc60_upperLines (bc57_pt k 1) := by
-- proof
  apply StatMech.Walls.bc88_upperLines_isTrifurcation_general k

/--
[bc88_open_nbr_of_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_open_nbr_of_center_eq
  {d : ℕ}
  {v : Site 2}
-- given
  (hadj : (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 1) v) :
-- imply
  v = bc57_pt 1 1 ∨ v = bc57_pt (-1) 1 := by
-- proof
  apply StatMech.Walls.bc88_open_nbr_of_center hadj

/--
[bc88_center_open_degree_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_center_open_degree_le_two_eq
  {d : ℕ}
  {Vset : Finset (Site 2)}
  {F : SimpleGraph (↑Vset : Type)}
  [DecidableRel F.Adj]
  {vx : (↑Vset : Type)}
-- given
  (hπ : ∀ u v, F.Adj u v → (openSubgraph 2 bc60_upperLines).Adj (u : Site 2) (v : Site 2))
  (hvx : (vx : Site 2) = bc57_pt 0 1) :
-- imply
  F.degree vx ≤ 2 := by
-- proof
  apply StatMech.Walls.bc88_center_open_degree_le_two F hπ vx hvx

/--
[bc88_upperLines_open_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_upperLines_open_degree_two_eq
  {d : ℕ}
  {Vset : Finset (Site 2)}
  {F : SimpleGraph (↑Vset : Type)}
  [DecidableRel F.Adj]
  {vx : (↑Vset : Type)}
-- given
  (hπ : ∀ u v, F.Adj u v → (openSubgraph 2 bc60_upperLines).Adj (u : Site 2) (v : Site 2))
  (hvx : (vx : Site 2) = bc57_pt 0 1) :
-- imply
  F.degree vx ≤ 2 := by
-- proof
  apply StatMech.Walls.bc88_upperLines_open_degree_two F hπ vx hvx

/--
[bc88_upperLines_boxOpenForest_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_upperLines_boxOpenForest_fails_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ bst_BoxOpenForest bc60_upperLines n := by
-- proof
  apply StatMech.Walls.bc88_upperLines_boxOpenForest_fails hn

/--
[bc88_coarse_fires_upperLines](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_coarse_fires_upperLines_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc88_coarse_fires_upperLines hL

/--
[bc88_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc88genuinecount.lean)
-/
@[path]
private lemma bc88_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), bst_BoxOpenForest ω n → Tcount 2 ω n ≤ boxSV_boundaryCard 2 n) ∧ (∀ k : ℤ, IsTrifurcation 2 bc60_upperLines (bc57_pt k 1)) ∧ (∀ n : ℕ, 1 ≤ n → ¬ bst_BoxOpenForest bc60_upperLines n) ∧ (∀ L : ℕ, 3 ≤ L → bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc88_status


-- created on 2026-10-23

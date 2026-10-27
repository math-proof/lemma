import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
open SimpleGraph Set StatMech StatMech.Lattice


/--
[whb_crossEdge_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_crossEdge_endpoints_eq
  {a b : Site 2} :
-- imply
  crossEdge s(a, b) = s(rot90Fun a, rot90Fun b) := by
-- proof
  apply StatMech.Lattice.whb_crossEdge_endpoints a b

/--
[whb_crossEdge_symm_straddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_crossEdge_symm_straddle_eq
  {f g : Site 2} :
-- imply
  crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
-- proof
  apply StatMech.Lattice.whb_crossEdge_symm_straddle f g

/--
[whb_imageGraph_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_imageGraph_square_eq :
-- imply
  imageGraph jbc_Pce = jei_pushGraph jbc_Pce jbc_cyc4 := by
-- proof
  apply StatMech.Lattice.whb_imageGraph_square

/--
[whb_reg_adj_of_straddle_ym1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_reg_adj_of_straddle_ym1_eq
  {f g : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj f g)
  (h : (rot90Inv f) 1 = -1 ∨ (rot90Inv g) 1 = -1) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Adj f g := by
-- proof
  apply StatMech.Lattice.whb_reg_adj_of_straddle_ym1 hadj h

/--
[whb_latadj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_latadj_eq
  {a b : Site 2}
-- given
  (h : (∑ i, (a i - b i).natAbs) = 1) :
-- imply
  (hypercubicLattice 2).Adj a b := by
-- proof
  apply StatMech.Lattice.whb_latadj h

/--
[whb_csq_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_csq_x_eq
  {i : Fin 4} :
-- imply
  (jbc_csq i) 0 = 0 ∨ (jbc_csq i) 0 = 1 := by
-- proof
  apply StatMech.Lattice.whb_csq_x i

/--
[whb_pushed_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_pushed_corner_eq
  {u v : Site 2}
-- given
  (h : (jei_pushGraph jbc_Pce jbc_cyc4).Adj u v) :
-- imply
  (u 0 = 0 ∨ u 0 = 1) ∧ (u 1 = 0 ∨ u 1 = 1) := by
-- proof
  apply StatMech.Lattice.whb_pushed_corner h

/--
[whb_east_step_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_east_step_safe_eq
  {a b : ℤ}
-- given
  (h : ¬ (a = -1 ∧ (b = 0 ∨ b = 1))) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a + 1, b] := by
-- proof
  apply StatMech.Lattice.whb_east_step_safe a b h

/--
[whb_south_step_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_south_step_safe_eq
  {a b : ℤ}
-- given
  (hsafe : ¬ (b = 1 ∧ (a = 0 ∨ a = -1))) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.whb_south_step_safe a b hsafe

/--
[whb_north_step_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_north_step_safe_eq
  {a b : ℤ}
-- given
  (hb : b ≠ 0) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a, b + 1] := by
-- proof
  apply StatMech.Lattice.whb_north_step_safe a b hb

/--
[whb_west_step_safe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_west_step_safe_eq
  {a b : ℤ}
-- given
  (ha : a ≠ 0) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Adj ![a, b] ![a - 1, b] := by
-- proof
  apply StatMech.Lattice.whb_west_step_safe a b ha

/--
[whb_up_to_m2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_up_to_m2_eq
  {a : ℤ} :
-- imply
  ∀ n : ℕ, (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2 - (n : ℤ)] ![a, -2] := by
-- proof
  apply StatMech.Lattice.whb_up_to_m2 a

/--
[whb_south_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_south_reach_eq
  {a b : ℤ}
-- given
  (hsafe : ¬ (b = 1 ∧ (a = 0 ∨ a = -1))) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, b - 1] := by
-- proof
  apply StatMech.Lattice.whb_south_reach a b hsafe

/--
[whb_south_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_south_escape_eq
  {a b : ℤ}
-- given
  (hb : b ≤ 0) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, -2] := by
-- proof
  apply StatMech.Lattice.whb_south_escape a b hb

/--
[whb_east_reach_m2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_east_reach_m2_eq
  {a : ℤ} :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2] ![a + 1, -2] := by
-- proof
  apply StatMech.Lattice.whb_east_reach_m2 a

/--
[whb_row_to_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_row_to_beacon_eq
  {a : ℤ} :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, -2] ![0, -2] := by
-- proof
  apply StatMech.Lattice.whb_row_to_beacon a

/--
[whb_descend_safe_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_descend_safe_col_eq
  {a : ℤ}
  {b : ℤ}
-- given
  (ha : a ≠ 0 ∧ a ≠ -1) :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a, -2] := by
-- proof
  apply StatMech.Lattice.whb_descend_safe_col a ha b

/--
[whb_reaches_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_reaches_row_eq
  {a b : ℤ} :
-- imply
  ∃ a' : ℤ, (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![a', -2] := by
-- proof
  apply StatMech.Lattice.whb_reaches_row a b

/--
[whb_reaches_beacon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_reaches_beacon_eq
  {a b : ℤ} :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable ![a, b] ![0, -2] := by
-- proof
  apply StatMech.Lattice.whb_reaches_beacon a b

/--
[whb_square_regionGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_square_regionGraph_connected_eq
  {x y : Site 2} :
-- imply
  (regionGraph (imageGraph jbc_Pce)).Reachable x y := by
-- proof
  apply StatMech.Lattice.whb_square_regionGraph_connected x y

/--
[whb_square_card_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_square_card_components_eq :
-- imply
  Nat.card (regionGraph (imageGraph jbc_Pce)).ConnectedComponent = 1 := by
-- proof
  apply StatMech.Lattice.whb_square_card_components

/--
[whb_square_faceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_square_faceCount_eq :
-- imply
  faceCount jbc_cyc4 = 2 := by
-- proof
  apply StatMech.Lattice.whb_square_faceCount

/--
[whb_planarCutCycleDuality_square_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_planarCutCycleDuality_square_false_eq :
-- imply
  ¬ jsf_PlanarCutCycleDuality jbc_Pce := by
-- proof
  apply StatMech.Lattice.whb_planarCutCycleDuality_square_false

/--
[whb_faceRegion_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_faceRegion_adj_eq
  {G : SimpleGraph (Site 2)}
  {f g : Site 2} :
-- imply
  (whb_faceRegion G).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet := by
-- proof
  apply StatMech.Lattice.whb_faceRegion_adj G f g

/--
[whb_square_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_square_edge_mem_eq
  {u v : Fin 4}
-- given
  (h : jbc_cyc4.Adj u v) :
-- imply
  s(jbc_csq u, jbc_csq v) ∈ (imageGraph jbc_Pce).edgeSet := by
-- proof
  apply StatMech.Lattice.whb_square_edge_mem h

/--
[whb_faceRegion_interior_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_faceRegion_interior_isolated_eq
  {g : Site 2} :
-- imply
  ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g := by
-- proof
  apply StatMech.Lattice.whb_faceRegion_interior_isolated g

/--
[whb_faceRegion_interior_supp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_faceRegion_interior_supp_eq :
-- imply
  ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp = {![0, 0]} := by
-- proof
  apply StatMech.Lattice.whb_faceRegion_interior_supp

/--
[whb_faceRegion_interior_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_faceRegion_interior_bounded_eq :
-- imply
  ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite := by
-- proof
  apply StatMech.Lattice.whb_faceRegion_interior_bounded

/--
[whb_correctModel_square_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_correctModel_square_separates_eq :
-- imply
  (∀ g, ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g) ∧ ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite := by
-- proof
  apply StatMech.Lattice.whb_correctModel_square_separates

/--
[whb_loop_crossing_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_loop_crossing_even_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Lattice.whb_loop_crossing_even S w

/--
[whb_barrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_barrier_separates_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ Even (crossCount S w) := by
-- proof
  apply StatMech.Lattice.whb_barrier_separates S hx hy w

/--
[whb_latticeMinusBarrier_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean)
-/
@[path]
private lemma whb_latticeMinusBarrier_separates_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ (latticeMinusBarrier S).Reachable x y := by
-- proof
  apply StatMech.Lattice.whb_latticeMinusBarrier_separates S hx hy


-- created on 2026-10-23

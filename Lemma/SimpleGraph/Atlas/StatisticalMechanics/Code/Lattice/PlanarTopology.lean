import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[nearestNeighbour_iff_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma nearestNeighbour_iff_shift_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  NearestNeighbour d x y ↔ ∃ j : Fin d, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ y = shift d x j s := by
-- proof
  apply StatMech.Lattice.nearestNeighbour_iff_shift d x y

/--
[adj_candMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma adj_candMap_eq
  {d : ℕ}
  {x : Site d}
  {p : Fin d × Bool} :
-- imply
  (hypercubicLattice d).Adj x (candMap d x p) := by
-- proof
  apply StatMech.Lattice.adj_candMap d x p

/--
[mem_candFinset_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma mem_candFinset_of_adj_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (h : (hypercubicLattice d).Adj x y) :
-- imply
  y ∈ candFinset d x := by
-- proof
  apply StatMech.Lattice.mem_candFinset_of_adj d x y h

/--
[candMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma candMap_injective_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Function.Injective (candMap d x) := by
-- proof
  apply StatMech.Lattice.candMap_injective d x

/--
[neighborFinset_eq_candFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma neighborFinset_eq_candFinset_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  (hypercubicLattice d).neighborFinset x = candFinset d x := by
-- proof
  apply StatMech.Lattice.neighborFinset_eq_candFinset d x

/--
[card_candFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_candFinset_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  (candFinset d x).card = 2 * d := by
-- proof
  apply StatMech.Lattice.card_candFinset d x

/--
[degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma degree_eq_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  (hypercubicLattice d).degree x = 2 * d := by
-- proof
  apply StatMech.Lattice.degree_eq d x

/--
[isRegularOfDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma isRegularOfDegree_eq
  {d : ℕ} :
-- imply
  (hypercubicLattice d).IsRegularOfDegree (2 * d) := by
-- proof
  apply StatMech.Lattice.isRegularOfDegree d

/--
[degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma degree_le_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  (hypercubicLattice d).degree x ≤ 2 * d := by
-- proof
  apply StatMech.Lattice.degree_le d x

/--
[card_finsetWalkLength_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_finsetWalkLength_le_eq
  {G : SimpleGraph V}
  [DecidableEq V]
  [SimpleGraph.LocallyFinite G]
  {D : ℕ}
  {n : ℕ}
  {u v : V}
-- given
  (hD : ∀ v, G.degree v ≤ D) :
-- imply
  (G.finsetWalkLength n u v).card ≤ D ^ n := by
-- proof
  apply StatMech.Lattice.card_finsetWalkLength_le G hD n u v

/--
[card_finsetWalkLength_self_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_finsetWalkLength_self_le_eq
  {G : SimpleGraph V}
  [DecidableEq V]
  [SimpleGraph.LocallyFinite G]
  {D : ℕ}
  {n : ℕ}
  {v : V}
-- given
  (hD : ∀ v, G.degree v ≤ D) :
-- imply
  (G.finsetWalkLength n v v).card ≤ D ^ n := by
-- proof
  apply StatMech.Lattice.card_finsetWalkLength_self_le G hD n v

/--
[card_circuits_based_in_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_circuits_based_in_le_eq
  {G : SimpleGraph V}
  [DecidableEq V]
  [SimpleGraph.LocallyFinite G]
  {D : ℕ}
  {B : Finset V}
  {n : ℕ}
-- given
  (hD : ∀ v, G.degree v ≤ D) :
-- imply
  (B.sigma (fun v => G.finsetWalkLength n v v)).card ≤ B.card * D ^ n := by
-- proof
  apply StatMech.Lattice.card_circuits_based_in_le G hD B n

/--
[card_finsetWalkLength_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_finsetWalkLength_le_pow_eq
  {d n : ℕ}
  {u v : Site d} :
-- imply
  ((hypercubicLattice d).finsetWalkLength n u v).card ≤ (2 * d) ^ n := by
-- proof
  apply StatMech.Lattice.card_finsetWalkLength_le_pow d n u v

/--
[card_circuits_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_circuits_le_pow_eq
  {d n : ℕ}
  {v : Site d} :
-- imply
  ((hypercubicLattice d).finsetWalkLength n v v).card ≤ (2 * d) ^ n := by
-- proof
  apply StatMech.Lattice.card_circuits_le_pow d n v

/--
[card_circuits_based_in_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_circuits_based_in_le_pow_eq
  {d : ℕ}
  {B : Finset (Site d)}
  {n : ℕ} :
-- imply
  (B.sigma (fun v => (hypercubicLattice d).finsetWalkLength n v v)).card ≤ B.card * (2 * d) ^ n := by
-- proof
  apply StatMech.Lattice.card_circuits_based_in_le_pow d B n

/--
[card_dual_circuits_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma card_dual_circuits_le_pow_eq
  {n : ℕ}
  {v : Site 2} :
-- imply
  (dualLattice.finsetWalkLength n v v).card ≤ 4 ^ n := by
-- proof
  apply StatMech.Lattice.card_dual_circuits_le_pow n v

/--
[l1dist_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma l1dist_self_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  l1dist d x x = 0 := by
-- proof
  apply StatMech.Lattice.l1dist_self d x

/--
[l1dist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma l1dist_comm_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  l1dist d x y = l1dist d y x := by
-- proof
  apply StatMech.Lattice.l1dist_comm d x y

/--
[l1dist_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma l1dist_of_adj_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (h : (hypercubicLattice d).Adj x y) :
-- imply
  l1dist d x y = 1 := by
-- proof
  apply StatMech.Lattice.l1dist_of_adj d h

/--
[l1dist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma l1dist_triangle_eq
  {d : ℕ}
  {x y z : Site d} :
-- imply
  l1dist d x z ≤ l1dist d x y + l1dist d y z := by
-- proof
  apply StatMech.Lattice.l1dist_triangle d x y z

/--
[l1dist_le_walk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma l1dist_le_walk_length_eq
  {d : ℕ}
  {x y : Site d}
  {w : (hypercubicLattice d).Walk x y} :
-- imply
  l1dist d x y ≤ w.length := by
-- proof
  apply StatMech.Lattice.l1dist_le_walk_length d w

/--
[mem_support_l1dist_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma mem_support_l1dist_le_eq
  {d : ℕ}
  {x y : Site d}
  {w : (hypercubicLattice d).Walk x y}
  {z : Site d}
-- given
  (hz : z ∈ w.support) :
-- imply
  l1dist d x z ≤ w.length := by
-- proof
  apply StatMech.Lattice.mem_support_l1dist_le d w hz

/--
[circuit_support_subset_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean)
-/
@[path]
private lemma circuit_support_subset_ball_eq
  {d n : ℕ}
  {v : Site d}
  {w : (hypercubicLattice d).Walk v v}
-- given
  (hw : w.length = n) :
-- imply
  ∀ z ∈ w.support, l1dist d v z ≤ n := by
-- proof
  apply StatMech.Lattice.circuit_support_subset_ball d n v w hw


-- created on 2026-10-23

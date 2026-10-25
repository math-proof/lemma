import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicCoverageShells
open Filter Finset Set SimpleGraph StatMech StatMech.FrontierD


/--
[mem_fkQgt4SquarePeriodicConnectionShellPairs_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma mem_fkQgt4SquarePeriodicConnectionShellPairs_dist_eq
  {n : Nat}
  {xy : square.BufferedVertex (2 * n) × square.BufferedVertex (2 * n)}
-- given
  (hxy : xy ∈ fkQgt4SquarePeriodicConnectionShellPairs n) :
-- imply
  n ≤ square.graph.dist xy.1.1 xy.2.1 := by
-- proof
  apply StatMech.FrontierD.mem_fkQgt4SquarePeriodicConnectionShellPairs_dist n xy hxy

/--
[fkQgt4SquarePeriodicConnectionShellPairs_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma fkQgt4SquarePeriodicConnectionShellPairs_card_le_eq
  {n : Nat} :
-- imply
  (fkQgt4SquarePeriodicConnectionShellPairs n).card ≤ 625 * (n + 1) ^ 4 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SquarePeriodicConnectionShellPairs_card_le n

/--
[mem_fkQgt4AxisAnchoredSphereConnectionEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma mem_fkQgt4AxisAnchoredSphereConnectionEvent_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat} :
-- imply
  omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent n ↔ ∃ z : Site 2, StatMech.Lattice.Connected 2 omega (axisSite n) z ∧ l1dist 2 (axisSite n) z = n := by
-- proof
  apply StatMech.FrontierD.mem_fkQgt4AxisAnchoredSphereConnectionEvent_iff omega n

/--
[mem_box_two_mul_of_l1dist_axis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma mem_box_two_mul_of_l1dist_axis_le_eq
  {n : Nat}
  {z : Site 2}
-- given
  (hz : l1dist 2 (axisSite n) z ≤ n) :
-- imply
  z ∈ box 2 (2 * n) := by
-- proof
  apply StatMech.FrontierD.mem_box_two_mul_of_l1dist_axis_le n hz

/--
[l1dist_le_square_graph_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma l1dist_le_square_graph_dist_eq
  {x y : Site 2} :
-- imply
  l1dist 2 x y ≤ square.graph.dist x y := by
-- proof
  apply StatMech.FrontierD.l1dist_le_square_graph_dist x y

/--
[fkQgt4AxisAnchoredSphereConnectionEvent_subset_periodicShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma fkQgt4AxisAnchoredSphereConnectionEvent_subset_periodicShell_eq
  {n : Nat} :
-- imply
  fkQgt4AxisAnchoredSphereConnectionEvent n ⊆ square.bufferedPairShell (2 * n) (fkQgt4SquarePeriodicConnectionShellPairs n) := by
-- proof
  apply StatMech.FrontierD.fkQgt4AxisAnchoredSphereConnectionEvent_subset_periodicShell n

/--
[inverseDualHasInfiniteClusterEvent_compl_subset_periodicShell_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma inverseDualHasInfiniteClusterEvent_compl_subset_periodicShell_limsup_eq :
-- imply
  inverseDualHasInfiniteClusterEventᶜ ⊆ limsup (fun n => square.bufferedPairShell (2 * n) (fkQgt4SquarePeriodicConnectionShellPairs n)) atTop := by
-- proof
  apply StatMech.FrontierD.inverseDualHasInfiniteClusterEvent_compl_subset_periodicShell_limsup

/--
[inverseDualHasInfiniteClusterEvent_eq_square_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma inverseDualHasInfiniteClusterEvent_eq_square_preimage_eq :
-- imply
  inverseDualHasInfiniteClusterEvent = inverseFaceDualConfig ⁻¹' {eta | square.HasInfiniteCluster eta} := by
-- proof
  apply StatMech.FrontierD.inverseDualHasInfiniteClusterEvent_eq_square_preimage

/--
[inverseFaceDual_square_planar_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicCoverageShells.lean)
-/
@[path]
private lemma inverseFaceDual_square_planar_limsup_eq :
-- imply
  (inverseFaceDualConfig ⁻¹' {eta | square.HasInfiniteCluster eta})ᶜ ⊆ limsup (fun n => square.bufferedPairShell (2 * n) (fkQgt4SquarePeriodicConnectionShellPairs n)) atTop := by
-- proof
  apply StatMech.FrontierD.inverseFaceDual_square_planar_limsup


-- created on 2026-10-23

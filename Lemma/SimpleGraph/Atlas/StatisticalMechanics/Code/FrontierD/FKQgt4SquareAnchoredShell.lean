import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[measurable_inverseFaceDualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma measurable_inverseFaceDualConfig_eq :
-- imply
  Measurable (inverseFaceDualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) := by
-- proof
  apply StatMech.FrontierD.measurable_inverseFaceDualConfig

/--
[fci_faceDualConfig_inverseFaceDualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma fci_faceDualConfig_inverseFaceDualConfig_eq
  {omega : ConfigSpace (Sym2 (Site 2))} :
-- imply
  fci_faceDualConfig (inverseFaceDualConfig omega) = omega := by
-- proof
  apply StatMech.FrontierD.fci_faceDualConfig_inverseFaceDualConfig omega

/--
[inverseFaceDualConfig_fci_faceDualConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma inverseFaceDualConfig_fci_faceDualConfig_eq
  {eta : ConfigSpace (Sym2 (Site 2))} :
-- imply
  inverseFaceDualConfig (fci_faceDualConfig eta) = eta := by
-- proof
  apply StatMech.FrontierD.inverseFaceDualConfig_fci_faceDualConfig eta

/--
[squareRegionConfig_mk_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma squareRegionConfig_mk_eq_true_eq
  {K : Set (Site 2)}
  {x y : Site 2} :
-- imply
  squareRegionConfig K s(x, y) = true ↔ x ∈ K ∧ y ∈ K := by
-- proof
  apply StatMech.FrontierD.squareRegionConfig_mk_eq_true K x y

/--
[squareRegionConfig_cluster_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma squareRegionConfig_cluster_eq_eq
  {K : Set (Site 2)}
-- given
  (hzero : origin 2 ∈ K)
  (hconn : ∀ a b : K, ((hypercubicLattice 2).induce K).Reachable a b) :
-- imply
  cluster 2 (squareRegionConfig K) (origin 2) = K := by
-- proof
  apply StatMech.FrontierD.squareRegionConfig_cluster_eq K hzero hconn

/--
[latticeWalk_hits_l1Sphere](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma latticeWalk_hits_l1Sphere_eq
  {center : Site 2}
  {a b : Site 2}
  {w : (hypercubicLattice 2).Walk a b}
  {n : Nat}
-- given
  (ha : l1dist 2 center a ≤ n)
  (hb : n ≤ l1dist 2 center b) :
-- imply
  ∃ z ∈ w.support, l1dist 2 center z = n := by
-- proof
  apply StatMech.FrontierD.latticeWalk_hits_l1Sphere center w n ha hb

/--
[measurableSet_fkQgt4CriticalFreeSphereConnectionEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma measurableSet_fkQgt4CriticalFreeSphereConnectionEvent_eq
  {j : Nat} :
-- imply
  MeasurableSet (fkQgt4CriticalFreeSphereConnectionEvent j) := by
-- proof
  apply StatMech.FrontierD.measurableSet_fkQgt4CriticalFreeSphereConnectionEvent j

/--
[fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {j : Nat}
-- given
  (htrans : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site 2)) mu) :
-- imply
  mu (fkQgt4AxisAnchoredSphereConnectionEvent j) = mu (fkQgt4CriticalFreeSphereConnectionEvent j) := by
-- proof
  apply StatMech.FrontierD.fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq mu htrans j

/--
[fkQgt4SiteRadius_sub_axisSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma fkQgt4SiteRadius_sub_axisSite_eq
  {j : Nat}
  {z : Site 2} :
-- imply
  fkQgt4SiteRadius (z - axisSite j) = l1dist 2 (axisSite j) z := by
-- proof
  apply StatMech.FrontierD.fkQgt4SiteRadius_sub_axisSite j z

/--
[mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {j : Nat}
  {z : Site 2}
-- given
  (hconn : Connected 2 omega (axisSite j) z)
  (hdist : l1dist 2 (axisSite j) z = j) :
-- imply
  omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent j := by
-- proof
  apply StatMech.FrontierD.mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected omega j hconn hdist

/--
[squareBoxClusterUnion_open_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma squareBoxClusterUnion_open_closed_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
  {x y : Site 2}
-- given
  (hx : x ∈ squareBoxClusterUnion eta n)
  (hxy : (openSubgraph 2 eta).Adj x y) :
-- imply
  y ∈ squareBoxClusterUnion eta n := by
-- proof
  apply StatMech.FrontierD.squareBoxClusterUnion_open_closed eta n hx hxy

/--
[squareHoleFill_open_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma squareHoleFill_open_closed_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hS : S.Finite)
  (hclosed : ∀ {x y}, x ∈ S → (openSubgraph 2 eta).Adj x y → y ∈ S)
  (hx : x ∈ squareHoleFill S hS)
  (hxy : (openSubgraph 2 eta).Adj x y) :
-- imply
  y ∈ squareHoleFill S hS := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_open_closed eta S hS hclosed hx hxy

/--
[squareHoleFill_inverseDual_faceBoundaryGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma squareHoleFill_inverseDual_faceBoundaryGraph_le_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
-- given
  (hS : S.Finite)
  (hclosed : ∀ {x y}, x ∈ S → (openSubgraph 2 (inverseFaceDualConfig omega)).Adj x y → y ∈ S) :
-- imply
  faceBoundaryGraph (squareHoleFill S hS) ≤ openSubgraph 2 omega := by
-- proof
  apply StatMech.FrontierD.squareHoleFill_inverseDual_faceBoundaryGraph_le omega S hS hclosed

/--
[exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (inverseFaceDualConfig omega) x).Finite) :
-- imply
  ∃ j ≥ n, omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent j := by
-- proof
  apply StatMech.FrontierD.exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite omega n hfinite

/--
[measurableSet_inverseDualHasInfiniteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma measurableSet_inverseDualHasInfiniteClusterEvent_eq :
-- imply
  MeasurableSet inverseDualHasInfiniteClusterEvent := by
-- proof
  apply StatMech.FrontierD.measurableSet_inverseDualHasInfiniteClusterEvent

/--
[inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup_eq :
-- imply
  inverseDualHasInfiniteClusterEventᶜ ⊆ limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop := by
-- proof
  apply StatMech.FrontierD.inverseDualHasInfiniteClusterEvent_compl_subset_axis_limsup

/--
[fkQgt4CriticalFreeAxisAnchoredSphereConnectionEvent_limsup_zero_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeAxisAnchoredSphereConnectionEvent_limsup_zero_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (limsup fkQgt4AxisAnchoredSphereConnectionEvent atTop) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeAxisAnchoredSphereConnectionEvent_limsup_zero_of_winding hq hwind

/--
[fkQgt4CriticalFree_inverseDualHasInfiniteClusterEvent_eq_one_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_inverseDualHasInfiniteClusterEvent_eq_one_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) inverseDualHasInfiniteClusterEvent = 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_inverseDualHasInfiniteClusterEvent_eq_one_of_winding hq hwind


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualPercolation
open Filter MeasureTheory Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq_eq
  {mu : Measure (ConfigSpace (Sym2 (Site 2)))}
  {j : Nat}
-- given
  (htrans : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site 2)) mu) :
-- imply
  mu (fkQgt4FaceDualAnchoredSphereConnectionEvent j) = mu (fkQgt4CriticalFreeSphereConnectionEvent j) := by
-- proof
  apply StatMech.FrontierD.fkQgt4FaceDualAnchoredSphereConnectionEvent_measure_eq mu htrans j

/--
[mem_fkQgt4FaceDualAnchoredSphereConnectionEvent_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma mem_fkQgt4FaceDualAnchoredSphereConnectionEvent_of_connected_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {j : Nat}
  {z : Site 2}
-- given
  (hconn : Connected 2 omega (faceDualAxisAnchor j) z)
  (hdist : l1dist 2 (faceDualAxisAnchor j) z = j) :
-- imply
  omega ∈ fkQgt4FaceDualAnchoredSphereConnectionEvent j := by
-- proof
  apply StatMech.FrontierD.mem_fkQgt4FaceDualAnchoredSphereConnectionEvent_of_connected omega j hconn hdist

/--
[exists_faceDualAnchoredSphereConnection_of_clusters_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma exists_faceDualAnchoredSphereConnection_of_clusters_finite_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {n : Nat}
-- given
  (hfinite : ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite) :
-- imply
  ∃ j ≥ n, omega ∈ fkQgt4FaceDualAnchoredSphereConnectionEvent j := by
-- proof
  apply StatMech.FrontierD.exists_faceDualAnchoredSphereConnection_of_clusters_finite omega n hfinite

/--
[faceDual_allFinite_subset_anchored_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma faceDual_allFinite_subset_anchored_limsup_eq :
-- imply
  {omega : ConfigSpace (Sym2 (Site 2)) | ∀ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Finite} ⊆ limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop := by
-- proof
  apply StatMech.FrontierD.faceDual_allFinite_subset_anchored_limsup

/--
[fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_ratePos hq hpos

/--
[fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_ratePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_ratePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  let mu := ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) mu {omega | ∃ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_ratePos hq hpos

/--
[fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (limsup fkQgt4FaceDualAnchoredSphereConnectionEvent atTop) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4FaceDualAnchoredSphereConnectionEvent_limsup_zero_of_winding hq hwind

/--
[fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_winding_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hwind : FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q)) :
-- imply
  let mu := ((FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) mu {omega | ∃ x : Site 2, (cluster 2 (fci_faceDualConfig omega) x).Infinite} = 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_faceDual_hasInfiniteCluster_of_winding hq hwind


-- created on 2026-10-23

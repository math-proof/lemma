import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[isOpen_connectedEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma isOpen_connectedEvent_eq
  {d : Nat}
  {x y : Site d} :
-- imply
  IsOpen {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} := by
-- proof
  apply StatMech.FrontierB.isOpen_connectedEvent x y

/--
[finiteCluster_mem_finiteClusterNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma finiteCluster_mem_finiteClusterNeighborhood_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hfin : (cluster d omega x).Finite) :
-- imply
  cluster d omega x ⊆ (finiteClusterNeighborhood omega x hfin : Set (Site d)) := by
-- proof
  apply StatMech.FrontierB.finiteCluster_mem_finiteClusterNeighborhood omega x hfin

/--
[neighbor_mem_finiteClusterNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma neighbor_mem_finiteClusterNeighborhood_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {z w : Site d}
-- given
  (hfin : (cluster d omega x).Finite)
  (hz : z ∈ cluster d omega x)
  (hzw : (hypercubicLattice d).Adj z w) :
-- imply
  w ∈ finiteClusterNeighborhood omega x hfin := by
-- proof
  apply StatMech.FrontierB.neighbor_mem_finiteClusterNeighborhood omega x hfin hz hzw

/--
[clusterWithin_finiteClusterNeighborhood_eq_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma clusterWithin_finiteClusterNeighborhood_eq_cluster_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hfin : (cluster d omega x).Finite) :
-- imply
  clusterWithin d omega (finiteClusterNeighborhood omega x hfin : Set (Site d)) x = cluster d omega x := by
-- proof
  apply StatMech.FrontierB.clusterWithin_finiteClusterNeighborhood_eq_cluster omega x hfin

/--
[isClopen_finiteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma isClopen_finiteClusterEvent_eq
  {d : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hfin : (cluster d omega x).Finite) :
-- imply
  IsClopen (clusterEvent d (finiteClusterNeighborhood omega x hfin : Set (Site d)) x (cluster d omega x)) := by
-- proof
  apply StatMech.FrontierB.isClopen_finiteClusterEvent omega x hfin

/--
[connected_clusterEvent_imp_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma connected_clusterEvent_imp_mem_eq
  {d : Nat}
  {omega eta : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hfin : (cluster d omega x).Finite)
  (heta : eta ∈ clusterEvent d (finiteClusterNeighborhood omega x hfin : Set (Site d)) x (cluster d omega x))
  (hxy : Connected d eta x y) :
-- imply
  y ∈ cluster d omega x := by
-- proof
  apply StatMech.FrontierB.connected_clusterEvent_imp_mem omega eta x y hfin heta hxy

/--
[frontier_connectedEvent_subset_distinctInfiniteClusterEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma frontier_connectedEvent_subset_distinctInfiniteClusterEvent_eq
  {d : Nat}
  {x y : Site d} :
-- imply
  frontier {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} ⊆ distinctInfiniteClusterEvent x y := by
-- proof
  apply StatMech.FrontierB.frontier_connectedEvent_subset_distinctInfiniteClusterEvent x y

/--
[allClustersEven_iff_mark_reachability](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma allClustersEven_iff_mark_reachability_eq
  {d : Nat}
  {G : SimpleGraph V}
  {omega : ConfigSpace (Sym2 V)}
  {A : Finset V} :
-- imply
  AllClustersEven G omega A ↔ ∀ x ∈ A, Even (markReachableCount G omega A x) := by
-- proof
  apply StatMech.FrontierB.allClustersEven_iff_mark_reachability G omega A

/--
[allClustersEven_congr_of_mark_connectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma allClustersEven_congr_of_mark_connectivity_eq
  {d : Nat}
  {G : SimpleGraph V}
  {omega eta : ConfigSpace (Sym2 V)}
  {A : Finset V}
-- given
  (hconn : ∀ x ∈ A, ∀ y ∈ A, (openSub G omega).Reachable x y ↔ (openSub G eta).Reachable x y) :
-- imply
  AllClustersEven G omega A ↔ AllClustersEven G eta A := by
-- proof
  apply StatMech.FrontierB.allClustersEven_congr_of_mark_connectivity G omega eta A hconn

/--
[frontier_allClustersEvenEvent_subset_atLeastTwoInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma frontier_allClustersEvenEvent_subset_atLeastTwoInfinite_eq
  {d : Nat}
  {A : Finset (Site d)} :
-- imply
  frontier (allClustersEvenEvent (hypercubicLattice d) A) ⊆ atLeastTwoInfinite d := by
-- proof
  apply StatMech.FrontierB.frontier_allClustersEvenEvent_subset_atLeastTwoInfinite A

/--
[measure_frontier_allClustersEvenEvent_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma measure_frontier_allClustersEvenEvent_eq_zero_eq
  {d : Nat}
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {A : Finset (Site d)}
-- given
  (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0) :
-- imply
  (mu : Measure _) (frontier (allClustersEvenEvent (hypercubicLattice d) A)) = 0 := by
-- proof
  apply StatMech.FrontierB.measure_frontier_allClustersEvenEvent_eq_zero mu hunique A

/--
[measurable_markReachableCount_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma measurable_markReachableCount_lattice_eq
  {d : Nat}
  {A : Finset (Site d)}
  {x : Site d} :
-- imply
  Measurable (fun omega : ConfigSpace (Sym2 (Site d)) => markReachableCount (hypercubicLattice d) omega A x) := by
-- proof
  apply StatMech.FrontierB.measurable_markReachableCount_lattice A x

/--
[measurableSet_allClustersEvenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma measurableSet_allClustersEvenEvent_eq
  {d : Nat}
  {A : Finset (Site d)} :
-- imply
  MeasurableSet (allClustersEvenEvent (hypercubicLattice d) A) := by
-- proof
  apply StatMech.FrontierB.measurableSet_allClustersEvenEvent A

/--
[WeakConvergesTo.tendsto_real_of_null_frontier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean)
-/
@[path]
private lemma tendsto_real_of_null_frontier_eq
  {d : Nat}
  [Countable E]
  {mu : Nat → ProbabilityMeasure (ConfigSpace E)}
  {nu : ProbabilityMeasure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
-- given
  (h : WeakConvergesTo mu nu)
  (hA : (nu : Measure _) (frontier A) = 0) :
-- imply
  Tendsto (fun n => (mu n : Measure _).real A) atTop (nhds ((nu : Measure _).real A)) := by
-- proof
  apply StatMech.FrontierB.WeakConvergesTo.tendsto_real_of_null_frontier h hA


-- created on 2026-10-23

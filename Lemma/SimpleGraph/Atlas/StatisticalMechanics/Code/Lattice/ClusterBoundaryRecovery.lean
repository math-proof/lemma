import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.ClusterBoundaryRecovery
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[edgeStraddles_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma edgeStraddles_mk_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d} :
-- imply
  edgeStraddles K s(x, y) ↔ (x ∈ K ↔ y ∉ K) := by
-- proof
  apply StatMech.Lattice.edgeStraddles_mk K x y

/--
[edgeStraddles_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma edgeStraddles_comm_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d} :
-- imply
  edgeStraddles K s(x, y) ↔ edgeStraddles K s(y, x) := by
-- proof
  apply StatMech.Lattice.edgeStraddles_comm K x y

/--
[latticeMinusBoundary_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma latticeMinusBoundary_adj_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d} :
-- imply
  (latticeMinusBoundary K).Adj x y ↔ (hypercubicLattice d).Adj x y ∧ ¬ edgeStraddles K s(x, y) := by
-- proof
  apply StatMech.Lattice.latticeMinusBoundary_adj K x y

/--
[latticeMinusBoundary_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma latticeMinusBoundary_le_eq
  {d : ℕ}
  {K : Set (Site d)} :
-- imply
  latticeMinusBoundary K ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Lattice.latticeMinusBoundary_le K

/--
[barrier_sameComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma barrier_sameComponent_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d}
  {w : (latticeMinusBoundary K).Walk x y} :
-- imply
  (x ∈ K ↔ y ∈ K) := by
-- proof
  apply StatMech.Lattice.barrier_sameComponent K w

/--
[not_reachable_in_barrier_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma not_reachable_in_barrier_of_separated_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ K)
  (hy : y ∉ K) :
-- imply
  ¬ (latticeMinusBoundary K).Reachable x y := by
-- proof
  apply StatMech.Lattice.not_reachable_in_barrier_of_separated K hx hy

/--
[latticeOn_le_latticeMinusBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma latticeOn_le_latticeMinusBoundary_eq
  {d : ℕ}
  {K : Set (Site d)} :
-- imply
  latticeOn K ≤ latticeMinusBoundary K := by
-- proof
  apply StatMech.Lattice.latticeOn_le_latticeMinusBoundary K

/--
[reachable_in_barrier_of_latticeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma reachable_in_barrier_of_latticeOn_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d}
-- given
  (h : (latticeOn K).Reachable x y) :
-- imply
  (latticeMinusBoundary K).Reachable x y := by
-- proof
  apply StatMech.Lattice.reachable_in_barrier_of_latticeOn K h

/--
[reachable_in_barrier_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma reachable_in_barrier_of_mem_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {x : Site d}
-- given
  (hK : IsConnectedCluster K)
  (hx : x ∈ K) :
-- imply
  (latticeMinusBoundary (↑K : Set (Site d))).Reachable (origin d) x := by
-- proof
  apply StatMech.Lattice.reachable_in_barrier_of_mem hK hx

/--
[connectedCluster_eq_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma connectedCluster_eq_component_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {x : Site d}
-- given
  (hK : IsConnectedCluster K) :
-- imply
  x ∈ (↑K : Set (Site d)) ↔ (latticeMinusBoundary (↑K : Set (Site d))).Reachable (origin d) x := by
-- proof
  apply StatMech.Lattice.connectedCluster_eq_component hK x

/--
[edgeStraddles_iff_mem_boundaryEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma edgeStraddles_iff_mem_boundaryEdgeSet_eq
  {d : ℕ}
  {K : Set (Site d)}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  edgeStraddles K s(x, y) ↔ s(x, y) ∈ boundaryEdgeSet K := by
-- proof
  apply StatMech.Lattice.edgeStraddles_iff_mem_boundaryEdgeSet K hadj

/--
[latticeMinusBoundary_eq_of_boundaryEdgeSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma latticeMinusBoundary_eq_of_boundaryEdgeSet_eq_eq
  {d : ℕ}
  {K₁ K₂ : Set (Site d)}
-- given
  (h : boundaryEdgeSet K₁ = boundaryEdgeSet K₂) :
-- imply
  latticeMinusBoundary K₁ = latticeMinusBoundary K₂ := by
-- proof
  apply StatMech.Lattice.latticeMinusBoundary_eq_of_boundaryEdgeSet_eq h

/--
[connCluster_eq_of_boundaryEdgeSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma connCluster_eq_of_boundaryEdgeSet_eq_eq
  {d : ℕ}
  {K₁ K₂ : Finset (Site d)}
-- given
  (hK₁ : IsConnectedCluster K₁)
  (hK₂ : IsConnectedCluster K₂)
  (h : boundaryEdgeSet (↑K₁ : Set (Site d)) = boundaryEdgeSet (↑K₂ : Set (Site d))) :
-- imply
  K₁ = K₂ := by
-- proof
  apply StatMech.Lattice.connCluster_eq_of_boundaryEdgeSet_eq hK₁ hK₂ h

/--
[boundaryEdgeSet_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterBoundaryRecovery.lean)
-/
@[path]
private lemma boundaryEdgeSet_injective_eq
  {d : ℕ} :
-- imply
  Set.InjOn (fun K : Finset (Site d) => boundaryEdgeSet (↑K : Set (Site d))) {K | IsConnectedCluster K} := by
-- proof
  apply StatMech.Lattice.boundaryEdgeSet_injective


-- created on 2026-10-23

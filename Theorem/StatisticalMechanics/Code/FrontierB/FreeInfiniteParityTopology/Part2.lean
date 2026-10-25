/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeInfiniteParityTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityNoEscape.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem finiteCluster_mem_finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    cluster d omega x ⊆
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) := by
  intro z hz
  apply Finset.mem_coe.2
  apply Finset.mem_union_left
  exact (hfin.mem_toFinset).2 hz

theorem neighbor_mem_finiteClusterNeighborhood
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) {z w : Site d}
    (hz : z ∈ cluster d omega x) (hzw : (hypercubicLattice d).Adj z w) :
    w ∈ finiteClusterNeighborhood omega x hfin := by
  classical
  apply Finset.mem_union_right
  rw [Finset.mem_biUnion]
  exact ⟨z, (hfin.mem_toFinset).2 hz,
    (SimpleGraph.mem_neighborFinset (hypercubicLattice d) z w).2 hzw⟩

theorem clusterWithin_finiteClusterNeighborhood_eq_cluster
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    clusterWithin d omega (finiteClusterNeighborhood omega x hfin : Set (Site d)) x =
      cluster d omega x := by
  classical
  let S : Set (Site d) := finiteClusterNeighborhood omega x hfin
  ext y
  constructor
  · rintro hy
    exact hy.2.2.connected
  · intro hy
    obtain ⟨w⟩ := (mem_cluster.1 hy)
    have hsupp : ∀ z ∈ w.support, z ∈ S := by
      intro z hz
      apply finiteCluster_mem_finiteClusterNeighborhood omega x hfin
      exact mem_cluster.2 (w.takeUntil z hz).reachable
    have hxS : x ∈ S := hsupp x w.start_mem_support
    have hyS : y ∈ S := hsupp y w.end_mem_support
    exact ⟨hyS, hxS, ⟨w.induce S hsupp⟩⟩

theorem isClopen_finiteClusterEvent
    (omega : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hfin : (cluster d omega x).Finite) :
    IsClopen (clusterEvent d
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) x
      (cluster d omega x)) := by
  classical
  let S := finiteClusterNeighborhood omega x hfin
  let K := hfin.toFinset
  have hxS : x ∈ (S : Set (Site d)) :=
    finiteCluster_mem_finiteClusterNeighborhood omega x hfin
      (self_mem_cluster omega x)
  have hK : (K : Set (Site d)) = cluster d omega x := hfin.coe_toFinset
  have hdep := clusterEvent_dependsOn (d := d) (S := S) (K := K) hxS
  rw [hK] at hdep
  rw [eq_cylinder_restrict_image _ _ hdep]
  exact isClopen_cylinderEvent _ _

theorem connected_clusterEvent_imp_mem
    (omega eta : ConfigSpace (Sym2 (Site d))) (x y : Site d)
    (hfin : (cluster d omega x).Finite)
    (heta : eta ∈ clusterEvent d
      (finiteClusterNeighborhood omega x hfin : Set (Site d)) x
      (cluster d omega x))
    (hxy : Connected d eta x y) : y ∈ cluster d omega x := by
  classical
  let S : Set (Site d) := finiteClusterNeighborhood omega x hfin
  have hcluster : clusterWithin d eta S x = cluster d omega x := heta
  obtain ⟨w⟩ := hxy
  have hx : x ∈ cluster d omega x := self_mem_cluster omega x
  have trap : ∀ {u v : Site d}, (openSubgraph d eta).Walk u v →
      u ∈ cluster d omega x → v ∈ cluster d omega x := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | @cons u v z huv p ih =>
      intro hu
      have hvS : v ∈ S := by
        apply neighbor_mem_finiteClusterNeighborhood omega x hfin hu
        exact (show IsOpenEdge d eta u v from huv).1
      have huWithin : u ∈ clusterWithin d eta S x := by
        rw [hcluster]
        exact hu
      have hvWithin : v ∈ clusterWithin d eta S x :=
        clusterWithin_closed huWithin hvS (show IsOpenEdge d eta u v from huv)
      have hv : v ∈ cluster d omega x := by rwa [hcluster] at hvWithin
      exact ih hv
  exact trap w hx


theorem frontier_connectedEvent_subset_distinctInfiniteClusterEvent (x y : Site d) :
    frontier {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y} ⊆
      distinctInfiniteClusterEvent x y := by
  intro omega homega
  have hopen := isOpen_connectedEvent x y
  have hnotconn : ¬ Connected d omega x y := by
    intro hconn
    apply homega.2
    rw [hopen.interior_eq]
    exact hconn
  have hinfinite (z w : Site d) (hzw : ¬ Connected d omega z w)
      (hclosure : omega ∈ closure
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w}) :
      (cluster d omega z).Infinite := by
    intro hfin
    let U := clusterEvent d
      (finiteClusterNeighborhood omega z hfin : Set (Site d)) z
      (cluster d omega z)
    have homegaU : omega ∈ U :=
      clusterWithin_finiteClusterNeighborhood_eq_cluster omega z hfin
    have hUopen : IsOpen U := (isClopen_finiteClusterEvent omega z hfin).isOpen
    have hdisj : Disjoint U
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w} := by
      rw [Set.disjoint_left]
      intro eta heta hconn
      exact hzw (mem_cluster.1
        (connected_clusterEvent_imp_mem omega eta z w hfin heta hconn))
    have hnotclosure : omega ∉ closure
        {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta z w} := by
      intro hclosure'
      obtain ⟨eta, hetaU, hetaConn⟩ :=
        (mem_closure_iff.1 hclosure') U hUopen homegaU
      exact (Set.disjoint_left.1 hdisj) hetaU hetaConn
    exact hnotclosure hclosure
  have homega_rev : omega ∈ frontier
      {eta : ConfigSpace (Sym2 (Site d)) | Connected d eta y x} := by
    simpa only [connected_comm] using homega
  exact ⟨hinfinite x y hnotconn homega.1,
    hinfinite y x (fun hyx => hnotconn hyx.symm) homega_rev.1, hnotconn⟩

end StatMech.FrontierB

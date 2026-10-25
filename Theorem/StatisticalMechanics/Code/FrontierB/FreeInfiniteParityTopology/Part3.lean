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
import Def.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FrontierB

open ConfigSpace FK Lattice Percolation

variable {d : Nat}

theorem allClustersEven_iff_mark_reachability
    {V : Type*} (G : SimpleGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Finset V) :
    AllClustersEven G omega A ↔
      ∀ x ∈ A, Even (markReachableCount G omega A x) := by
  classical
  constructor
  · intro h x hx
    have hh := h ((openSub G omega).connectedComponentMk x)
    simpa only [clusterMarkCount, markReachableCount,
      SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm] using hh
  · intro h C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ z =>
      by_cases hex : ∃ x ∈ A, (openSub G omega).Reachable z x
      · obtain ⟨x, hxA, hzx⟩ := hex
        have hcomp : (openSub G omega).connectedComponentMk z =
            (openSub G omega).connectedComponentMk x :=
          SimpleGraph.ConnectedComponent.sound hzx
        rw [hcomp]
        simpa only [clusterMarkCount, markReachableCount,
          SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm] using h x hxA
      · have hempty : A.filter
            (fun x => (openSub G omega).connectedComponentMk x =
              (openSub G omega).connectedComponentMk z) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.2
          intro x hx
          rw [Finset.mem_filter, SimpleGraph.ConnectedComponent.eq] at hx
          exact hex ⟨x, hx.1, hx.2.symm⟩
        simp only [clusterMarkCount, hempty, Finset.card_empty]
        norm_num

theorem allClustersEven_congr_of_mark_connectivity
    {V : Type*} (G : SimpleGraph V)
    (omega eta : ConfigSpace (Sym2 V)) (A : Finset V)
    (hconn : ∀ x ∈ A, ∀ y ∈ A,
      (openSub G omega).Reachable x y ↔ (openSub G eta).Reachable x y) :
    AllClustersEven G omega A ↔ AllClustersEven G eta A := by
  rw [allClustersEven_iff_mark_reachability,
    allClustersEven_iff_mark_reachability]
  constructor <;> intro h x hx
  · have heq : markReachableCount G omega A x =
        markReachableCount G eta A x := by
      unfold markReachableCount
      congr 1
      ext y
      simp only [Finset.mem_filter]
      exact and_congr_right fun hy => hconn x hx y hy
    rw [← heq]
    exact h x hx
  · have heq : markReachableCount G eta A x =
        markReachableCount G omega A x := by
      unfold markReachableCount
      congr 1
      ext y
      simp only [Finset.mem_filter]
      exact and_congr_right fun hy => (hconn x hx y hy).symm
    rw [← heq]
    exact h x hx

end StatMech.FrontierB

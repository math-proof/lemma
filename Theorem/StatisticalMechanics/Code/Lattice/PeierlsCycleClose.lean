/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem pcy_toSubgraph_neighbor_of_fourThin {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hthin : mci_FourThin Vc) {u v : Site 2} (hu : u ∈ Vc.support) (hv : v ∈ Vc.support)
    (hadj : (hypercubicLattice 2).Adj u v) :
    v ∈ Vc.toSubgraph.neighborSet u := by
  rw [Subgraph.mem_neighborSet, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  exact hthin u v hu hv hadj


theorem pcy_thickPoint_of_three_support_neighbors {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hcyc : Vc.IsCycle)
    {u v₁ v₂ v₃ : Site 2} (hu : u ∈ Vc.support)
    (h1 : (hypercubicLattice 2).Adj u v₁) (h2 : (hypercubicLattice 2).Adj u v₂)
    (h3 : (hypercubicLattice 2).Adj u v₃)
    (hv1 : v₁ ∈ Vc.support) (hv2 : v₂ ∈ Vc.support) (hv3 : v₃ ∈ Vc.support)
    (hne12 : v₁ ≠ v₂) (hne13 : v₁ ≠ v₃) (hne23 : v₂ ≠ v₃) :
    kns_ThickPoint Vc := by
  rw [kns_thickPoint_iff_not_fourThin]
  intro hthin
  have m1 : v₁ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv1 h1
  have m2 : v₂ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv2 h2
  have m3 : v₃ ∈ Vc.toSubgraph.neighborSet u :=
    pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv3 h3
  have hcard := hcyc.ncard_neighborSet_toSubgraph_eq_two hu
  have hfin : (Vc.toSubgraph.neighborSet u).Finite := Vc.finite_neighborSet_toSubgraph
  have hsub : ({v₁, v₂, v₃} : Set (Site 2)) ⊆ Vc.toSubgraph.neighborSet u := by
    intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h3card : ({v₁, v₂, v₃} : Set (Site 2)).ncard = 3 := by
    rw [Set.ncard_eq_three]; exact ⟨v₁, v₂, v₃, hne12, hne13, hne23, rfl⟩
  have hle := Set.ncard_le_ncard hsub hfin
  rw [h3card, hcard] at hle
  omega


theorem pcy_le_two_support_neighbors {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (hthin : mci_FourThin Vc) {u : Site 2} (hu : u ∈ Vc.support) :
    {v : Site 2 | (hypercubicLattice 2).Adj u v ∧ v ∈ Vc.support}.ncard ≤ 2 := by
  have hsub : {v : Site 2 | (hypercubicLattice 2).Adj u v ∧ v ∈ Vc.support}
      ⊆ Vc.toSubgraph.neighborSet u := by
    rintro v ⟨hadj, hv⟩
    exact pcy_toSubgraph_neighbor_of_fourThin Vc hthin hu hv hadj
  have hfin : (Vc.toSubgraph.neighborSet u).Finite := Vc.finite_neighborSet_toSubgraph
  have hle := Set.ncard_le_ncard hsub hfin
  rwa [hcyc.ncard_neighborSet_toSubgraph_eq_two hu] at hle


theorem pcy_thickPoint_of_WES {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) {x y : ℤ}
    (hu : (![x, y] : Site 2) ∈ Vc.support)
    (hW : (![x - 1, y] : Site 2) ∈ Vc.support)
    (hE : (![x + 1, y] : Site 2) ∈ Vc.support)
    (hS : (![x, y - 1] : Site 2) ∈ Vc.support) :
    kns_ThickPoint Vc := by
  refine pcy_thickPoint_of_three_support_neighbors Vc hcyc hu
    (v₁ := (![x - 1, y] : Site 2)) (v₂ := (![x + 1, y] : Site 2)) (v₃ := (![x, y - 1] : Site 2))
    ?_ ?_ ?_ hW hE hS ?_ ?_ ?_
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega
  · intro h; have := congrFun h 1; simp at this; omega
  · intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega


end Lattice
end StatMech

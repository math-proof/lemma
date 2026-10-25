/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanContour.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exterior_reachable_in_barrier (K : Set (Site 2)) (R : ℕ) (hK : K ⊆ box 2 R)
    {x y : Site 2} (hx : x ∈ exterior 2 R) (hy : y ∈ exterior 2 R) :
    (latticeMinusBarrier K).Reachable x y := by
  have hsub : exterior 2 R ⊆ Kᶜ := exterior_subset_compl K R hK
  have hmap := (box_exterior_connected R (by norm_num) x y hx hy).map (extToBarrierHom K R hsub)
  simpa [extToBarrierHom] using hmap


theorem outsideComponent_infinite (K : Set (Site 2)) (R : ℕ) (hK : K ⊆ box 2 R) :
    ((latticeMinusBarrier K).connectedComponentMk (beacon 2 R)).supp.Infinite := by
  have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => ((w : Site 2))) ?_ ?_
  · intro a b hab; exact Subtype.ext hab
  · intro w
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact exterior_reachable_in_barrier K R hK w.2 hbe


theorem cluster_inside_not_reachable_outside (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∉ cluster 2 ω o) :
    ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y :=
  not_reachable_latticeMinusBarrier (cluster 2 ω o) hx hy


theorem inside_ne_outside_component (o : Site 2) (R : ℕ) (hR : cluster 2 ω o ⊆ box 2 R) :
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ≠
      (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) := by
  intro h
  rw [SimpleGraph.ConnectedComponent.eq] at h
  have hbe : beacon 2 R ∉ cluster 2 ω o := by
    have : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
    exact (exterior_subset_compl (cluster 2 ω o) R hR) this
  exact not_reachable_latticeMinusBarrier (cluster 2 ω o) (self_mem_cluster ω o) hbe h


theorem barrier_sameSide_of_reachable (S : Set (Site 2)) {x y : Site 2}
    (h : (latticeMinusBarrier S).Reachable x y) : (x ∈ S ↔ y ∈ S) := by
  obtain ⟨w⟩ := h
  exact latticeMinusBarrier_sameSide S w


theorem barrier_separates (S : Set (Site 2)) :
    (∀ ⦃x y : Site 2⦄, (latticeMinusBarrier S).Reachable x y → (x ∈ S ↔ y ∈ S)) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ S → y ∉ S → ¬ (latticeMinusBarrier S).Reachable x y) :=
  ⟨fun _ _ h => barrier_sameSide_of_reachable S h,
   fun _ _ hx hy => not_reachable_latticeMinusBarrier S hx hy⟩


theorem discrete_jordan_separation (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ R : ℕ, cluster 2 ω o ⊆ box 2 R ∧
      (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∈ cluster 2 ω o →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ exterior 2 R → y ∈ exterior 2 R →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) ∧
      (∀ ⦃x y : Site 2⦄, x ∈ cluster 2 ω o → y ∉ cluster 2 ω o →
        ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable x y) := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  exact ⟨R, hR,
    fun _ _ hx hy => cluster_reachable_in_barrier o hx hy,
    fun _ _ hx hy => exterior_reachable_in_barrier _ R hR hx hy,
    fun _ _ hx hy => not_reachable_latticeMinusBarrier _ hx hy⟩


theorem discrete_jordan_components (o : Site 2) (hfin : (cluster 2 ω o).Finite) :
    ∃ (R : ℕ)
      (_ : cluster 2 ω o ⊆ box 2 R)
      (Cin Cout : (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent),
      Cin = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o ∧
      Cout = (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R) ∧
      Cin.supp.Finite ∧ Cout.supp.Infinite ∧ Cin ≠ Cout ∧
      cluster 2 ω o ⊆ Cin.supp ∧ exterior 2 R ⊆ Cout.supp := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  refine ⟨R, hR,
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk o,
    (latticeMinusBarrier (cluster 2 ω o)).connectedComponentMk (beacon 2 R),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · 
    exact hfin.subset (insideComponent_supp_subset_cluster (ω := ω) o)
  · 
    exact outsideComponent_infinite (cluster 2 ω o) R hR
  · 
    exact inside_ne_outside_component (ω := ω) o R hR
  · 
    intro z hz
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact cluster_reachable_in_barrier o hz (self_mem_cluster ω o)
  · 
    intro z hz
    have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
    rw [ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact exterior_reachable_in_barrier (cluster 2 ω o) R hR hz hbe


end Lattice
end StatMech

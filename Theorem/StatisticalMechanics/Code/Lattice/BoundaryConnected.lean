/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)


variable {d : ℕ}


theorem exterior_mem_infiniteComponent (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x : Site d} (hx : x ∈ exterior d R) :
    (((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨x, exterior_subset_compl F R hR hx⟩).supp.Infinite := by
  classical
  set G := (hypercubicLattice d).induce Fᶜ with hG
  have hsub : exterior d R ⊆ Fᶜ := exterior_subset_compl F R hR
  set C := G.connectedComponentMk ⟨x, hsub hx⟩ with hC
  have : Infinite ↥(exterior d R) := (exterior_infinite R hd).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior d R) => (⟨(w : Site d), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
  · intro a b hab
    exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  · intro w
    rw [ConnectedComponent.mem_supp_iff, hC]
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R hd hsub (w : Site d) x w.2 hx)


theorem exterior_reachable_in_compl (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x y : Site d} (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).Reachable
      ⟨x, exterior_subset_compl F R hR hx⟩ ⟨y, exterior_subset_compl F R hR hy⟩ :=
  exterior_reachable_compl F R hd (exterior_subset_compl F R hR) x y hx hy


theorem exterior_connectedComponent_eq (hd : 2 ≤ d) (F : Set (Site d)) (R : ℕ)
    (hR : F ⊆ box d R) {x y : Site d} (hx : x ∈ exterior d R) (hy : y ∈ exterior d R) :
    ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨x, exterior_subset_compl F R hR hx⟩
      = ((hypercubicLattice d).induce Fᶜ).connectedComponentMk
        ⟨y, exterior_subset_compl F R hR hy⟩ :=
  ConnectedComponent.sound (exterior_reachable_in_compl hd F R hR hx hy)


variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem clusterComplement_unique_infiniteComponent (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃! C : ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).ConnectedComponent,
      C.supp.Infinite :=
  unique_infinite_component (by norm_num) (cluster 2 ω (origin 2)) hfin


theorem exists_clusterBox (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R :=
  finite_subset_box _ hfin


theorem axisFarRight_mem_exterior (R : ℕ) : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  show R < (((R : ℤ) + 1)).natAbs
  rw [show ((R : ℤ) + 1).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring]
  omega


theorem axisFarLeft_mem_exterior (R : ℕ) : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  show R < ((-((R : ℤ) + 1))).natAbs
  rw [show (-((R : ℤ) + 1)).natAbs = R + 1 by rw [Int.natAbs_eq_iff]; right; push_cast; ring]
  omega


theorem axisFar_sameComponent (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![(R : ℤ) + 1, 0],
          exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩
      = ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![-((R : ℤ) + 1), 0],
          exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ :=
  exterior_connectedComponent_eq (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R) (axisFarLeft_mem_exterior R)


theorem axisFar_reachable_in_clusterComplement (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩
      ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (axisFarLeft_mem_exterior R)⟩ :=
  exterior_reachable_in_compl (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R) (axisFarLeft_mem_exterior R)


theorem axisFarRight_infiniteComponent (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).connectedComponentMk
        ⟨![(R : ℤ) + 1, 0],
          exterior_subset_compl _ R hR (axisFarRight_mem_exterior R)⟩).supp.Infinite :=
  exterior_mem_infiniteComponent (by norm_num) (cluster 2 ω (origin 2)) R hR
    (axisFarRight_mem_exterior R)


end Lattice
end StatMech

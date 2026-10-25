/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Theorem.StatisticalMechanics.Code.Walls.kc3_offsupportreaches
import Theorem.StatisticalMechanics.Code.Walls.kc4_eulerone.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc4_orbitiscycle
import Def.StatisticalMechanics.Code.Walls.kc4_core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc4_reaches_exterior_of_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
    (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  classical
  set F := oc_supportSet Vc with hF
  set G := (hypercubicLattice 2).induce Fᶜ with hG
  have hFfin : F.Finite := Set.Finite.subset (box_finite 2 R) hsupp
  obtain ⟨C0, hC0inf, hC0uniq⟩ := unique_infinite_component (by norm_num) F hFfin
  have hzC : G.connectedComponentMk ⟨z, hzmem⟩ = C0 := hC0uniq _ hinf
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hsupp
  have hbext : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  set e : Site 2 := beacon 2 R with he
  have hemem : e ∈ Fᶜ := hsub hbext
  
  have heCinf : (G.connectedComponentMk ⟨e, hemem⟩).supp.Infinite := by
    have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
    refine Set.infinite_of_injective_forall_mem
      (f := fun w : ↥(exterior 2 R) => (⟨(w : Site 2), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
    · intro p q hpq; exact Subtype.ext (by simpa using congrArg Subtype.val hpq)
    · intro w
      rw [ConnectedComponent.mem_supp_iff]
      exact ConnectedComponent.sound
        (exterior_reachable_compl F R (by norm_num) hsub (w : Site 2) e w.2 hbext)
  have heC : G.connectedComponentMk ⟨e, hemem⟩ = C0 := hC0uniq _ heCinf
  
  have hzeReach : G.Reachable ⟨z, hzmem⟩ ⟨e, hemem⟩ := by
    rw [← ConnectedComponent.eq, hzC, heC]
  refine ⟨e, hbext, ?_⟩
  have := hzeReach.map (kc4_offSupportHom Vc)
  simpa [kc4_offSupportHom, hG, hF] using this


theorem kc4_extComponent_infinite (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {e : Site 2} (heExt : e ∈ exterior 2 R)
    (hemem : e ∈ (oc_supportSet Vc)ᶜ) :
    (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨e, hemem⟩).supp.Infinite := by
  classical
  set F := oc_supportSet Vc with hF
  set G := (hypercubicLattice 2).induce Fᶜ with hG
  have hsub : exterior 2 R ⊆ Fᶜ := exterior_subset_compl F R hsupp
  have : Infinite ↥(exterior 2 R) := (exterior_infinite R (by norm_num)).to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun w : ↥(exterior 2 R) => (⟨(w : Site 2), hsub w.2⟩ : ↥Fᶜ)) ?_ ?_
  · intro p q hpq; exact Subtype.ext (by simpa using congrArg Subtype.val hpq)
  · intro w
    rw [ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound
      (exterior_reachable_compl F R (by norm_num) hsub (w : Site 2) e w.2 heExt)


end Walls
end StatMech

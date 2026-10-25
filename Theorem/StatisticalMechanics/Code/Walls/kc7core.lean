/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc6core.Part2
import Theorem.StatisticalMechanics.Code.Walls.kc6uniqueinfinitecomponent
import Theorem.StatisticalMechanics.Code.Walls.kc6localconstancy
import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc7_even_of_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
    (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite) :
    z ∉ jec_leftRegion Vc := by
  
  obtain ⟨e, heExt, hreach⟩ :=
    kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf
  
  have hzoff : z ∉ Vc.support := by simpa [oc_supportSet] using hzmem
  
  obtain ⟨p, hp⟩ := (oc_offSupportLattice_reachable_iff Vc hzoff).mp hreach
  
  have hpar : (Even (jec_rayCount z Vc) ↔ Even (jec_rayCount e Vc)) :=
    oee_rayParity_const_along_walk Vc p hp
  
  have heEven : Even (jec_rayCount e Vc) := by
    have hsupp' : ∀ q ∈ Vc.support, q ∈ box 2 R := fun q hq => hsupp hq
    have hout : e ∉ jec_leftRegion Vc := oc_exterior_outside Vc R hsupp' heExt
    rw [jec_mem_leftRegion, not_not] at hout; exact hout
  
  rw [jec_mem_leftRegion, not_not]
  exact hpar.mpr heEven


theorem kc7_mem_compl_leftRegion_of_infiniteComponent (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzmem : z ∈ (oc_supportSet Vc)ᶜ)
    (hinf : (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite) :
    z ∈ (jec_leftRegion Vc)ᶜ :=
  kc7_even_of_infiniteComponent Vc R hsupp hzmem hinf


end Walls
end StatMech

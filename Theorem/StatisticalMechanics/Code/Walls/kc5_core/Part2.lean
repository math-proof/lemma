/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc4_core.Part2
import Def.StatisticalMechanics.Code.Walls.kc5_core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc5_offSupportReaches_of_corrected (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : kc5_OutsideOffSupportInfinite Vc) :
    kc5_OffSupportReachesExterior Vc R := by
  intro z hoff hout
  obtain ⟨hzmem, hinf⟩ := h z hoff hout
  exact kc4_reaches_exterior_of_infiniteComponent Vc R hsupp hzmem hinf


theorem kc5_corrected_seed (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    z ∉ Vc.support ∧ z ∉ jec_leftRegion Vc ∧
      ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
        (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
          ⟨z, hzmem⟩).supp.Infinite := by
  obtain ⟨hout, hzmem, hinf⟩ := kc4_residue_nonvacuous Vc R hsupp hz
  have hoff : z ∉ Vc.support := by
    simpa only [Set.mem_compl_iff, oc_mem_supportSet] using hzmem
  exact ⟨hoff, hout, hzmem, hinf⟩


theorem kc5_corrected_conclusion_seed (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ hzmem : z ∈ (oc_supportSet Vc)ᶜ,
      (((hypercubicLattice 2).induce (oc_supportSet Vc)ᶜ).connectedComponentMk
        ⟨z, hzmem⟩).supp.Infinite :=
  (kc5_corrected_seed Vc R hsupp hz).2.2

end Walls
end StatMech

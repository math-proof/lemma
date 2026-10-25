/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanKeepReconnect.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
import Def.StatisticalMechanics.Code.Lattice.JordanFiniteDetour.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfd_reconnect_split (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2)
    (hHR : ∀ v ∈ H.support, v ∈ box 2 R) (hf0 : f0 ∈ box 2 R) (hg0 : g0 ∈ box 2 R)
    (hcase : (∃ ef ∈ exterior 2 (R + 1),
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef) ∧
        (∃ eg ∈ exterior 2 (R + 1),
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg)) :
    ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  obtain ⟨⟨ef, hef, hfef⟩, ⟨eg, heg, hgeg⟩⟩ := hcase
  exact jfd_reconnect_of_both_escape H R f0 g0 hHR hf0 hg0 hef heg hfef hgeg


theorem jfd_sameComponent_iff_finiteKeep :
    jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue := Iff.rfl


theorem jfd_witnesses :
    
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    
    jkr_lineH.edgeSet.Infinite := by
  refine ⟨?_, ?_, ?_, jkr_lineH_edgeSet_infinite⟩
  · exact (jkr_witness_bot).2.2.2.2.2
  · exact (jkr_witness_square).2.2.2.2.2
  · exact (jkr_witness_ring).2.2.2.2.2


theorem jfd_status :
    
    (∀ (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2),
      (∀ v ∈ H.support, v ∈ box 2 R) → f0 ∈ box 2 R → g0 ∈ box 2 R →
      ∀ {ef eg : Site 2}, ef ∈ exterior 2 (R + 1) → eg ∈ exterior 2 (R + 1) →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg →
      ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) ∧
    
    (jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue) ∧
    
    (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) :=
  ⟨fun H R f0 g0 hHR hf0 hg0 {_ef _eg} hef heg hfef hgeg =>
      jfd_reconnect_of_both_escape H R f0 g0 hHR hf0 hg0 hef heg hfef hgeg,
    jfd_sameComponent_iff_finiteKeep,
    jkr_finite_of_keepReconnect⟩

end Lattice
end StatMech

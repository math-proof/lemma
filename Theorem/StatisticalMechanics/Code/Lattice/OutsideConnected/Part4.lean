/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OutsideConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem oc_outsideReachesExterior_of_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : oc_OutsideReachesTop Vc R) :
    oc_OutsideReachesExterior Vc R := by
  intro z hz
  obtain ⟨w, hwrow, p, hp⟩ := h z hz
  
  have hzoff : z ∉ Vc.support := hp z p.start_mem_support
  
  have hwoff : w ∉ Vc.support := hp w p.end_mem_support
  
  have hzw : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z w :=
    (oc_offSupportLattice_reachable_iff Vc hzoff).mpr ⟨p, hp⟩
  
  obtain ⟨e, heExt, hwe⟩ := oc_reachesExterior_of_row_ge_R Vc R hsupp hwrow hwoff
  exact ⟨e, heExt, hzw.trans hwe⟩


theorem oc_hOutOff_of_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : oc_OutsideReachesTop Vc R) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support :=
  oc_hOutOff_of_reachesExterior Vc R hsupp (oc_outsideReachesExterior_of_reachesTop Vc R hsupp h)


theorem oc_two_components_of_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hTop : oc_OutsideReachesTop Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  oc_two_components_of_outsideReaches Vc R hsupp hp hq hInOff
    (oc_outsideReachesExterior_of_reachesTop Vc R hsupp hTop)


theorem oc_top_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  refine ⟨z, hzrow, SimpleGraph.Walk.nil, ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
  exact hu ▸ hzoff


theorem oc_colClear_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  set e : Site 2 := ![z 0, (R : ℤ) + 1] with he
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, by rw [he]; simp, p, ?_⟩
  intro u hu
  rw [hp, SimpleGraph.Walk.support_copy] at hu
  exact oc_vertUp_clear_of_colClear Vc R hcol u hu


theorem oc_outsideReachesTop_of_outsideColClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hall : ∀ z : Site 2, z ∉ jec_leftRegion Vc →
        ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    oc_OutsideReachesTop Vc R := by
  intro z hz
  exact oc_colClear_reachesTop Vc R (hall z hz)

end Lattice
end StatMech

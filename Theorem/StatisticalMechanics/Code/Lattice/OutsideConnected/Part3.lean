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
import Def.StatisticalMechanics.Code.Lattice.OutsideConnected.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem oc_hOutOff_of_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (h : oc_OutsideReachesExterior Vc R) :
    ∀ s t : Site 2, s ∉ jec_leftRegion Vc → t ∉ jec_leftRegion Vc →
      ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support := by
  intro s t hs ht
  obtain ⟨es, hes, hreach_s⟩ := h s hs
  obtain ⟨et, het, hreach_t⟩ := h t ht
  
  
  have hsoff : s ∉ Vc.support := by
    rcases hreach_s with ⟨w⟩
    cases w with
    | nil => exact oc_exterior_offSupport Vc R hsupp hes
    | cons hadj _ => exact hadj.2.1
  
  have hmid : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable es et :=
    oc_exterior_reachable_offSupport Vc R hsupp hes het
  have hreach : (ffc_offSupportLattice (oc_supportSet Vc)).Reachable s t :=
    (hreach_s.trans hmid).trans hreach_t.symm
  exact (oc_offSupportLattice_reachable_iff Vc hsoff).mp hreach


theorem oc_two_components_of_outsideReaches (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R)
    {p q : Site 2} (hp : ¬ Even (jec_rayCount p Vc))
    (hq : ∀ w ∈ Vc.support, w 0 ≤ q 0 - 1)
    (hInOff : ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
        ∃ pw : (hypercubicLattice 2).Walk s t, ∀ z ∈ pw.support, z ∉ Vc.support)
    (hOut : oc_OutsideReachesExterior Vc R) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  jlri_two_components_of_offSupport_connected Vc hp hq hInOff
    (oc_hOutOff_of_reachesExterior Vc R hsupp hOut)


theorem oc_exterior_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  ⟨z, hz, SimpleGraph.Reachable.refl _⟩


theorem oc_mem_exterior_of_row_high (R : ℕ) {z : Site 2} (hz : (R : ℤ) + 1 ≤ z 1) :
    z ∈ exterior 2 R := by
  refine ⟨1, ?_⟩
  have h2 : (R : ℤ) < |z 1| := by
    have : (R : ℤ) < z 1 := by omega
    exact lt_of_lt_of_le this (le_abs_self _)
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2


theorem oc_mem_exterior_of_col_high (R : ℕ) {z : Site 2} (hz : (R : ℤ) + 1 ≤ z 0) :
    z ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  have h2 : (R : ℤ) < |z 0| := by
    have : (R : ℤ) < z 0 := by omega
    exact lt_of_lt_of_le this (le_abs_self _)
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2


theorem oc_reachesExterior_of_offSupport_walk (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z e : Site 2} (heExt : e ∈ exterior 2 R)
    (p : (hypercubicLattice 2).Walk z e) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    ∃ e' : Site 2, e' ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e' := by
  have hzoff : z ∉ Vc.support := hp z p.start_mem_support
  refine ⟨e, heExt, ?_⟩
  rw [oc_offSupportLattice_reachable_iff Vc hzoff]
  exact ⟨p, hp⟩


theorem oc_vertUpEscape (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
  set e : Site 2 := ![z 0, (R : ℤ) + 1] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_row_high R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, heExt, p, ?_⟩
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw


theorem oc_reachesExterior_of_vertUpClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  obtain ⟨e, heExt, p, hp⟩ := oc_vertUpEscape Vc R hclear
  exact oc_reachesExterior_of_offSupport_walk Vc R heExt p hp


theorem oc_horizRightEscape (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
  set e : Site 2 := ![(R : ℤ) + 1, z 1] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_col_high R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, heExt, p, ?_⟩
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw


theorem oc_reachesExterior_of_horizRightClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  obtain ⟨e, heExt, p, hp⟩ := oc_horizRightEscape Vc R hclear
  exact oc_reachesExterior_of_offSupport_walk Vc R heExt p hp


theorem oc_mem_exterior_of_row_low (R : ℕ) {z : Site 2} (hz : z 1 ≤ -((R : ℤ) + 1)) :
    z ∈ exterior 2 R := by
  refine ⟨1, ?_⟩
  have h2 : (R : ℤ) < |z 1| := by
    have : z 1 < -(R : ℤ) := by omega
    calc (R : ℤ) = -(-(R : ℤ)) := by ring
      _ < -(z 1) := by omega
      _ ≤ |z 1| := neg_le_abs _
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2


theorem oc_mem_exterior_of_col_low (R : ℕ) {z : Site 2} (hz : z 0 ≤ -((R : ℤ) + 1)) :
    z ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  have h2 : (R : ℤ) < |z 0| := by
    have : z 0 < -(R : ℤ) := by omega
    calc (R : ℤ) = -(-(R : ℤ)) := by ring
      _ < -(z 0) := by omega
      _ ≤ |z 0| := neg_le_abs _
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2


theorem oc_reachesExterior_of_vertDownClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  set e : Site 2 := ![z 0, -((R : ℤ) + 1)] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_row_low R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).copy hzeq.symm rfl with hp
  apply oc_reachesExterior_of_offSupport_walk Vc R heExt p
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw


theorem oc_reachesExterior_of_horizLeftClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  set e : Site 2 := ![-((R : ℤ) + 1), z 1] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_col_low R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).copy hzeq.symm rfl with hp
  apply oc_reachesExterior_of_offSupport_walk Vc R heExt p
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw


theorem oc_vertUp_support_col {z : Site 2} {R : ℕ} {w : Site 2}
    (hw : w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support) :
    ∃ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) ∧ w = ![z 0, t] :=
  (sw_vertSeg_mem_support (z 0) (z 1) ((R : ℤ) + 1) w).mp hw


theorem oc_vertUp_clear_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support := by
  intro w hw
  obtain ⟨t, ht, rfl⟩ := oc_vertUp_support_col hw
  exact hcol t ht


theorem oc_reachesExterior_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  oc_reachesExterior_of_vertUpClear Vc R (oc_vertUp_clear_of_colClear Vc R hcol)


theorem oc_reachesExterior_of_row_ge_R (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rcases lt_or_ge (R : ℤ) (z 1) with hlt | hge
  · 
    exact oc_exterior_reachesExterior Vc R (oc_mem_exterior_of_row_high R (by omega))
  · 
    
    have hzR : z 1 = R := le_antisymm hge hzrow
    apply oc_reachesExterior_of_colClear Vc R
    intro t ht hmem
    rw [Set.mem_uIcc] at ht
    
    have htbox : (![z 0, t] : Site 2) ∈ box 2 R := hsupp hmem
    have htabs : (t).natAbs ≤ R := by have := htbox 1; simpa using this
    have htle : t ≤ (R : ℤ) := by
      have : |t| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast htabs
      exact (abs_le.mp this).2
    
    have htR : t = (R : ℤ) := by omega
    subst htR
    
    have hzeq : (![z 0, (R : ℤ)] : Site 2) = z := by
      ext i; fin_cases i
      · simp
      · show (R : ℤ) = z 1; rw [hzR]
    rw [hzeq] at hmem
    exact hzoff hmem


end Lattice
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.kc9core
import Def.StatisticalMechanics.Code.Walls.kc10core
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {a : Site 2}


theorem kc10_support_row_le (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {s : Site 2} (hs : s ∈ Vc.support) :
    s 1 ≤ (R : ℤ) := by
  have hbox : s ∈ box 2 R := hsupp ((oc_mem_supportSet Vc s).mpr hs)
  have h1 : (s 1).natAbs ≤ R := hbox 1
  omega


theorem kc10_rightNb_offSupport_of_highRow (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2} (hrow : (R : ℤ) < z 1) :
    (![z 0 + 1, z 1] : Site 2) ∉ Vc.support := by
  intro hmem
  have h := kc10_support_row_le Vc R hsupp hmem
  have he : (![z 0 + 1, z 1] : Site 2) 1 = z 1 := by simp
  rw [he] at h
  omega


theorem kc10_rightStep_of_collarSlide (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hslide : kc10_CollarSlide Vc R) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  
  generalize hm : ((R : ℤ) + 1 - z 1).toNat = m
  induction m using Nat.strong_induction_on generalizing z with
  | _ m ih =>
    by_cases hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support
    · 
      have hrow : z 1 ≤ (R : ℤ) := by
        by_contra hgt
        exact kc10_rightNb_offSupport_of_highRow Vc R hsupp (by omega) hnb
      rcases hslide z hzout hzoff hzR hnb with hesc | hupOff
      · exact hesc
      · 
        set z' : Site 2 := ![z 0, z 1 + 1] with hz'
        have hstep : (offSupport Vc).Reachable z z' := kc9_upStep Vc hzoff hupOff
        have hz'off : z' ∉ Vc.support := hupOff
        have hz'out : z' ∉ jec_leftRegion Vc :=
          offSupport_component_monochromatic_out Vc hzout hstep hzoff
        have hz'R : z' 0 ≤ (R : ℤ) := by rw [hz']; simpa using hzR
        have hz'col : z' 0 = z 0 := by rw [hz']; simp
        have hz'row : z' 1 = z 1 + 1 := by rw [hz']; simp
        have hmw : ((R : ℤ) + 1 - z' 1).toNat < m := by
          rw [← hm, hz'row]; omega
        obtain ⟨w, hprog, hreach⟩ := ih _ hmw z' hz'out hz'off hz'R rfl
        refine ⟨w, ?_, hstep.trans hreach⟩
        rw [hz'col] at hprog; exact hprog
    · exact ⟨![z 0 + 1, z 1], by simp, ecc_rightNeighbor_step Vc hzoff hnb⟩


theorem kc10_rightDodge_of_collarSlide (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) (hslide : kc10_CollarSlide Vc R) :
    ecc_RightDodge Vc R := by
  intro z hzout hzoff hzR _
  exact kc10_rightStep_of_collarSlide Vc R hsupp hslide z hzout hzoff hzR


end Walls
end StatMech

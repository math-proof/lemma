/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wicinterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.wnbenoboundedeven
import Theorem.StatisticalMechanics.Code.Walls.wchcovering.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

variable {a : Site 2}


theorem wic_eta (w : Site 2) : (![w 0, w 1] : Site 2) = w := by
  funext i; fin_cases i <;> rfl


theorem wic_marchLeft (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
    {z : Site 2} (hz : z ∈ jec_leftRegion Vc) (hzoff : z ∉ Vc.support) :
    ∃ c₀ : ℤ, c₀ ≤ z 0 ∧
      (offSupport Vc).Reachable z (![c₀, z 1] : Site 2) ∧
      (![c₀, z 1] : Site 2) ∈ jec_leftRegion Vc ∧
      (![c₀, z 1] : Site 2) ∉ Vc.support ∧
      (![c₀ - 1, z 1] : Site 2) ∈ Vc.support := by
  classical
  set x := z 0 with hx
  set y := z 1 with hy
  have hzeta : (![x, y] : Site 2) = z := wic_eta z
  
  set P : ℤ → Prop := fun c => c ≤ x ∧ ∀ i ∈ Set.uIcc c x, (![i, y] : Site 2) ∉ Vc.support
    with hP
  
  have Hinh : ∃ c, P c := by
    refine ⟨x, le_refl _, ?_⟩
    intro i hi
    rw [Set.uIcc_self, Set.mem_singleton_iff] at hi
    subst hi
    rw [hzeta]; exact hzoff
  
  have Hreach : ∀ c, P c → (offSupport Vc).Reachable z (![c, y] : Site 2) := by
    intro c hc
    obtain ⟨hcle, hclear⟩ := hc
    have hrun : (offSupport Vc).Reachable (![c, y] : Site 2) (![x, y] : Site 2) := by
      have := wnbe_horizRun_reachable Vc y c x
      refine this ?_
      intro t ht; exact hclear t ht
    rw [hzeta] at hrun
    exact hrun.symm
  have Hinterior : ∀ c, P c → (![c, y] : Site 2) ∈ jec_leftRegion Vc := by
    intro c hc
    exact offSupport_component_monochromatic Vc hz (Hreach c hc) hzoff
  
  have Hbdd : ∃ b : ℤ, ∀ c : ℤ, P c → b ≤ c := by
    refine ⟨-(R : ℤ), ?_⟩
    intro c hc
    have hin : (![c, y] : Site 2) ∈ box 2 R :=
      egf_leftRegion_subset_box Vc R hsupp (Hinterior c hc)
    have h0 : ((![c, y] : Site 2) 0).natAbs ≤ R := hin 0
    have hcabs : (c).natAbs ≤ R := by simpa using h0
    omega
  
  obtain ⟨c₀, hPc₀, hmin⟩ := Int.exists_least_of_bdd Hbdd Hinh
  obtain ⟨hc₀le, hc₀clear⟩ := hPc₀
  refine ⟨c₀, hc₀le, ?_, ?_, ?_, ?_⟩
  · exact Hreach c₀ ⟨hc₀le, hc₀clear⟩
  · exact Hinterior c₀ ⟨hc₀le, hc₀clear⟩
  · exact hc₀clear c₀ (by rw [Set.uIcc_of_le hc₀le]; exact ⟨le_refl _, hc₀le⟩)
  · 
    by_contra hleftoff
    
    have hPc₀m1 : P (c₀ - 1) := by
      refine ⟨by linarith, ?_⟩
      intro i hi
      rw [Set.uIcc_of_le (by linarith : c₀ - 1 ≤ x), Set.mem_Icc] at hi
      obtain ⟨hlo, hhi⟩ := hi
      rcases lt_or_ge i c₀ with hic | hic
      · have : i = c₀ - 1 := by omega
        subst this; exact hleftoff
      · exact hc₀clear i (by rw [Set.uIcc_of_le hc₀le, Set.mem_Icc]; exact ⟨hic, hhi⟩)
    have := hmin (c₀ - 1) hPc₀m1
    omega


end Lattice
end StatMech

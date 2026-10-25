/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Def.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rlc_leftEndDescends_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_SegmentDown Vc seed) :
    rlc_LeftEndDescends Vc seed M := by
  intro z hz hzs hleft
  obtain ⟨cx, hxcx, hrun, hcdown⟩ := hres z hz hzs hleft
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hz ⊢
  have key := rlc_descend_via_segmentDown Vc M hMb (x := z 0) (y := z 1) (cx := cx) hz
    (by simpa using hxcx)
    (by intro t ht ht'; have := hrun t (by simpa using ht) ht'; simpa using this)
    (by simpa using hcdown)
  simpa using key


theorem rlc_rowLinked_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ)
    (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
    (hres : rlc_SegmentDown Vc seed) :
    jil_RowLinked Vc seed :=
  rlc_rowLinked_of_leftEndDescends Vc M hMb (rlc_leftEndDescends_of_segmentDown Vc M hMb hres)


theorem rlc_exists_rowLinked_seed_of_segmentDown {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
    (hres : ∀ seed : Site 2, rlc_SegmentDown Vc seed) :
    ∃ seed ∈ jil_offSupportInterior Vc, jil_RowLinked Vc seed := by
  obtain ⟨M, hMb⟩ := rlc_interior_bounded Vc
  obtain ⟨seed, hseed, _⟩ := rlc_exists_lexMin_seed Vc hz₀ M
  exact ⟨seed, hseed, rlc_rowLinked_of_segmentDown Vc M hMb (hres seed)⟩


theorem rlc_segmentDown_body_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z : Site 2} (hzoff : z ∉ Vc.support) (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z 0 ≤ cx ∧
      (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧
      (![cx, z 1 - 1] : Site 2) ∉ Vc.support := by
  refine ⟨z 0, le_rfl, ?_, hdown⟩
  intro t ht ht'
  have : t = z 0 := le_antisymm ht' ht
  subst this
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  rw [hzeq] at hzoff
  simpa using hzoff


theorem rlc_segmentDown_of_downOffSupport {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (seed : Site 2)
    (hdown : ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed →
      (![z 0 - 1, z 1] : Site 2) ∈ Vc.support → (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
    rlc_SegmentDown Vc seed := by
  intro z hz hzs hleft
  exact rlc_segmentDown_body_of_downOffSupport Vc
    (jil_mem_offSupportInterior Vc z |>.mp hz).1 (hdown z hz hzs hleft)


theorem rlc_segmentDown_body_multiCell {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z0 z1 : ℤ}
    (h0 : (![z0, z1] : Site 2) ∉ Vc.support)
    (h1 : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
    (hd : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
    ∃ cx : ℤ, z0 < cx ∧
      (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧
      (![cx, z1 - 1] : Site 2) ∉ Vc.support := by
  refine ⟨z0 + 1, by omega, ?_, hd⟩
  intro t ht ht'
  have : t = z0 ∨ t = z0 + 1 := by omega
  rcases this with h | h <;> subst h
  · exact h0
  · exact h1


theorem rlc_downLink_witness_ne {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (M : ℤ) (hdl : rlc_DownLink Vc seed M)
    {z : Site 2} (hz : z ∈ jil_offSupportInterior Vc) (hzs : z ≠ seed) :
    ∃ z' ∈ jil_offSupportInterior Vc, z' ≠ z ∧
      ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support := by
  obtain ⟨z', hz', hlt, p, hp⟩ := hdl z hz hzs
  refine ⟨z', hz', ?_, p, hp⟩
  intro hcon; rw [hcon] at hlt; exact (lt_irrefl _ hlt)

end Lattice
end StatMech

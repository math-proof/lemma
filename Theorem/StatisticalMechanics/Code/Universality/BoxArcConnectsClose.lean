/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Def.StatisticalMechanics.Code.Universality.BoxArcConnectsClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem bac_rightComplement_subset_boxMinusL (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    bac_rightComplement ω n ⊆ bac_boxMinusL ω n := fun _ hv => hv.choose


theorem bac_rightComplement_mem (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {v : Site 2}
    (hv : v ∈ bac_rightComplement ω n) : v ∈ rect 0 n 0 n ∧ v ∉ bcd_leftReach ω n :=
  bac_rightComplement_subset_boxMinusL ω n hv


theorem bac_rightWall_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {r : ℤ} (hr0 : 0 ≤ r) (hrn : r ≤ n) :
    (![n, r] : Site 2) ∈ bac_rightComplement ω n := by
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  have hyc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n :=
    ⟨rightSide_subset hyR, jex_rightSide_notin_leftReach ω n hnoH hyR⟩
  exact ⟨hyc, ![n, r], hyR, hyc, SimpleGraph.Reachable.refl _⟩


theorem bac_rightSegment_notMem_L (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (htr : mbc_IsRightFrontier ω n c r) {c' : ℤ} (hcc' : c < c') (hc'n : c' ≤ n) :
    (![c', r] : Site 2) ∉ bcd_leftReach ω n :=
  htr.2.2.2 c' hcc' hc'n


theorem bac_gap_mem_rightComplement (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    (![c + 1, r] : Site 2) ∈ bac_rightComplement ω n := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ n - (c + 1))
  
  have hseg : ∀ t : ℕ, t ≤ m →
      Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        ∈ bac_boxMinusL ω n := by
    intro t ht
    have hval : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (t : ℤ))
        = ![c + 1 + (t : ℤ), r] := by
      funext i; fin_cases i <;> simp [Function.update]
    rw [hval]
    have ht' : (t : ℤ) ≤ (m : ℤ) := by exact_mod_cast ht
    refine ⟨?_, ?_⟩
    · rw [mem_rect]
      refine ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩
    · exact bac_rightSegment_notMem_L ω n
        ⟨hc0, hcn, _hcL, _hmax⟩ (by omega) (by omega)
  
  have hreach := segment_connectedWithin (d := 2) (bac_boxMinusL ω n) (0 : Fin 2)
    (![c + 1, r] : Site 2) m hseg
  
  have e0 : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ))
      = ![c + 1, r] := by funext i; fin_cases i <;> simp [Function.update]
  have em : Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + (m : ℤ))
      = ![n, r] := by
    funext i
    fin_cases i
    · simp only [Function.update]; simp; omega
    · simp [Function.update]
  
  have hgapc : (![c + 1, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg 0 (Nat.zero_le m); rwa [e0] at this
  have hnc : (![n, r] : Site 2) ∈ bac_boxMinusL ω n := by
    have := hseg m le_rfl; rwa [em] at this
  have hn : 0 ≤ n := le_trans hr0 hrn
  have hyR : (![n, r] : Site 2) ∈ rightSide 0 n 0 n := by
    refine ⟨?_, by simp⟩
    rw [mem_rect]; exact ⟨by simp [hn], by simp, by simpa using hr0, by simpa using hrn⟩
  refine ⟨hgapc, ![n, r], hyR, hnc, ?_⟩
  
  have hsub0 : (⟨![c + 1, r], hgapc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((0 : ℕ) : ℤ)),
          hseg 0 (Nat.zero_le m)⟩ := Subtype.ext e0.symm
  have hsubm : (⟨![n, r], hnc⟩ : bac_boxMinusL ω n)
      = ⟨Function.update (![c + 1, r] : Site 2) 0 ((![c + 1, r] : Site 2) 0 + ((m : ℕ) : ℤ)),
          hseg m le_rfl⟩ := Subtype.ext em.symm
  rw [hsub0, hsubm]
  exact hreach


theorem bac_frontierFace_lowerRight (c r : ℤ) :
    faceCorner10 c r = ![c + 1, r] := rfl


end Universality
end StatMech

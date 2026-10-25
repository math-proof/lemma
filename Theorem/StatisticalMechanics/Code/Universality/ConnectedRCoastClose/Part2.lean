/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_corner_adj_or_diag {a b : ℤ} {p q : Site 2}
    (hp : p = ![a, b] ∨ p = ![a + 1, b] ∨ p = ![a, b + 1] ∨ p = ![a + 1, b + 1])
    (hq : q = ![a, b] ∨ q = ![a + 1, b] ∨ q = ![a, b + 1] ∨ q = ![a + 1, b + 1])
    (hne : p ≠ q) :
    (hypercubicLattice 2).Adj p q ∨ (p 0 ≠ q 0 ∧ p 1 ≠ q 1) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    solve
      | (exact absurd rfl hne)
      | (left; omega)
      | (right; refine ⟨?_, ?_⟩ <;> omega)


theorem crr_rCoastFace_has_interface_side (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {f : Site 2} (hf : bac_IsRCoastFace ω n f) :
    crr_HasInterfaceSide ω n f := by
  obtain ⟨hbarr, c, hcR, hcCorner⟩ := hf
  
  set a := f 0 with ha
  set b := f 1 with hb
  
  obtain ⟨u, v, hsides, hbd, hu, hv⟩ := crr_face_barrier_side ω n a b (by
    obtain ⟨g, hg⟩ := hbarr
    refine ⟨g, ?_⟩
    have : (![a, b] : Site 2) = f := by funext i; fin_cases i <;> simp [ha, hb]
    rwa [this])
  
  have huv_adj : (hypercubicLattice 2).Adj u v := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have huCorner : u = ![a, b] ∨ u = ![a + 1, b] ∨ u = ![a, b + 1] ∨ u = ![a + 1, b + 1] := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  have hvCorner : v = ![a, b] ∨ v = ![a + 1, b] ∨ v = ![a, b + 1] ∨ v = ![a + 1, b + 1] := by
    rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
  
  rw [bdEdge_mk] at hbd
  
  have hcCorner' : c = ![a, b] ∨ c = ![a + 1, b] ∨ c = ![a, b + 1] ∨ c = ![a + 1, b + 1] := by
    simpa [ha, hb] using hcCorner
  
  
  have mk : ∀ pL pR : Site 2, pL ∈ bcd_leftReach ω n → pR ∈ bac_rightComplement ω n →
      (hypercubicLattice 2).Adj pL pR → pL ∈ rect 0 n 0 n → pR ∈ rect 0 n 0 n →
      (pL = ![a, b] ∨ pL = ![a + 1, b] ∨ pL = ![a, b + 1] ∨ pL = ![a + 1, b + 1]) →
      (pR = ![a, b] ∨ pR = ![a + 1, b] ∨ pR = ![a, b + 1] ∨ pR = ![a + 1, b + 1]) →
      crr_HasInterfaceSide ω n f := by
    intro pL pR h1 h2 h3 h4 h5 h6 h7
    exact ⟨pL, pR, h1, h2, h3, h4, h5, by simpa [ha, hb] using h6, by simpa [ha, hb] using h7⟩
  
  by_cases huL : u ∈ bcd_leftReach ω n
  · 
    have hvnL : v ∉ bcd_leftReach ω n := hbd.mp huL
    by_cases hvR : v ∈ bac_rightComplement ω n
    · 
      exact mk u v huL hvR huv_adj hu hv huCorner hvCorner
    · 
      have hcv : c ≠ v := fun h => hvR (h ▸ hcR)
      have hnotadj : ¬ (hypercubicLattice 2).Adj c v := fun hadj =>
        hvR (crr_rightComplement_closed ω n hcR hadj hv hvnL)
      
      rcases crr_corner_adj_or_diag hcCorner' hvCorner hcv with hadj | hdiag
      · exact absurd hadj hnotadj
      · 
        have hcu_adj : (hypercubicLattice 2).Adj c u := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv_adj ⊢
          obtain ⟨hd0, hd1⟩ := hdiag
          rcases huCorner with rfl | rfl | rfl | rfl <;>
            rcases hvCorner with rfl | rfl | rfl | rfl <;>
            rcases hcCorner' with rfl | rfl | rfl | rfl <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huv_adj hd0 hd1 ⊢ <;> omega
        have hcbox : c ∈ rect 0 n 0 n := (bac_rightComplement_mem ω n hcR).1
        exact mk u c huL hcR hcu_adj.symm hu hcbox huCorner hcCorner'
  · 
    have hvL : v ∈ bcd_leftReach ω n := by
      by_cases hvL : v ∈ bcd_leftReach ω n
      · exact hvL
      · exact absurd (hbd.mpr hvL) huL
    have hunL : u ∉ bcd_leftReach ω n := huL
    by_cases huR : u ∈ bac_rightComplement ω n
    · exact mk v u hvL huR huv_adj.symm hv hu hvCorner huCorner
    · have hcu : c ≠ u := fun h => huR (h ▸ hcR)
      have hnotadj : ¬ (hypercubicLattice 2).Adj c u := fun hadj =>
        huR (crr_rightComplement_closed ω n hcR hadj hu hunL)
      rcases crr_corner_adj_or_diag hcCorner' huCorner hcu with hadj | hdiag
      · exact absurd hadj hnotadj
      · have hcv_adj : (hypercubicLattice 2).Adj c v := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv_adj ⊢
          obtain ⟨hd0, hd1⟩ := hdiag
          rcases huCorner with rfl | rfl | rfl | rfl <;>
            rcases hvCorner with rfl | rfl | rfl | rfl <;>
            rcases hcCorner' with rfl | rfl | rfl | rfl <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at huv_adj hd0 hd1 ⊢ <;> omega
        have hcbox : c ∈ rect 0 n 0 n := (bac_rightComplement_mem ω n hcR).1
        exact mk v c hvL hcR hcv_adj.symm hv hcbox hvCorner hcCorner'


theorem crr_hasInterfaceSide_pmdVertex (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f : Site 2}
    (h : crr_HasInterfaceSide ω n f) : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj f g := by
  obtain ⟨pL, pR, hpL, hpR, hadj, hpLbox, hpRbox, hpLc, hpRc⟩ := h
  have hbd : bdEdge (bcd_leftReach ω n) s(pL, pR) :=
    rcm_LR_edge_bdEdge ω n hpL hpR
  
  set a := f 0 with ha
  set b := f 1 with hb
  have hfe : f = ![a, b] := by funext i; fin_cases i <;> simp [ha, hb]
  
  rcases hpLc with rfl | rfl | rfl | rfl <;> rcases hpRc with rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two];
         simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      
      | (rw [hfe]; exact ⟨![a, b - 1], rcm_horizEdge_faces_pmdAdj ω n hbd hpLbox hpRbox⟩)
      | (rw [hfe]; exact ⟨![a, b - 1],
          (rcm_horizEdge_faces_pmdAdj ω n (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox)⟩)
      
      | (rw [hfe]; refine ⟨![a, b + 1], ?_⟩;
         have := rcm_horizEdge_faces_pmdAdj ω n (x := a) (y := b + 1) hbd hpLbox hpRbox;
         simpa using this.symm)
      | (rw [hfe]; refine ⟨![a, b + 1], ?_⟩;
         have := rcm_horizEdge_faces_pmdAdj ω n (x := a) (y := b + 1)
           (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox;
         simpa using this.symm)
      
      | (rw [hfe]; exact ⟨![a - 1, b], rcm_vertEdge_faces_pmdAdj ω n hbd hpLbox hpRbox⟩)
      | (rw [hfe]; exact ⟨![a - 1, b],
          rcm_vertEdge_faces_pmdAdj ω n (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox⟩)
      
      | (rw [hfe]; refine ⟨![a + 1, b], ?_⟩;
         have := rcm_vertEdge_faces_pmdAdj ω n (x := a + 1) (y := b) hbd hpLbox hpRbox;
         simpa using this.symm)
      | (rw [hfe]; refine ⟨![a + 1, b], ?_⟩;
         have := rcm_vertEdge_faces_pmdAdj ω n (x := a + 1) (y := b)
           (by rwa [Sym2.eq_swap] at hbd) hpRbox hpLbox;
         simpa using this.symm)


end Universality
end StatMech

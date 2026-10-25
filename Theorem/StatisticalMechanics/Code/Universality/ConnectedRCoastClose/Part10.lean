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
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part10
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_interfaceSide_reaches_interior
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f q : Site 2}
    (h : crr_InterfaceSideWith omega n f q) :
    ∃ f' : Site 2, f' ∈ rect 0 (n - 1) 0 (n - 1) ∧
      (crr_LRFaceGraph omega n).Reachable f f' ∧
      ∃ g, (crr_LRFaceGraph omega n).Adj f' g := by
  obtain ⟨g, hfg⟩ := crr_interfaceSideWith_LRNeighbor omega n h
  rcases crr_LRAdj_has_interior_endpoint hfg with hf | hg
  · exact ⟨f, hf, SimpleGraph.Reachable.refl _, g, hfg⟩
  · exact ⟨g, hg, hfg.reachable, f, hfg.symm⟩


theorem crr_interior_LRFaceGraph_reachable
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n)
    {f₁ f₂ : Site 2}
    (hf₁ : f₁ ∈ rect 0 (n - 1) 0 (n - 1))
    (hf₂ : f₂ ∈ rect 0 (n - 1) 0 (n - 1))
    (hinc₁ : ∃ g, (crr_LRFaceGraph omega n).Adj f₁ g)
    (hinc₂ : ∃ g, (crr_LRFaceGraph omega n).Adj f₂ g) :
    (crr_LRFaceGraph omega n).Reachable f₁ f₂ := by
  classical
  let P := crr_boxPlanar n
  let B := crr_boxRCut omega n
  let Rg := whb_faceRegion (imageGraph P)
  let O : Ising.kwg_Face P := Rg.connectedComponentMk ![-1, -1]
  let C₁ : Ising.kwg_Face P := Rg.connectedComponentMk f₁
  let C₂ : Ising.kwg_Face P := Rg.connectedComponentMk f₂
  obtain ⟨g₁, hfg₁⟩ := hinc₁
  obtain ⟨g₂, hfg₂⟩ := hinc₂
  obtain ⟨e₁, he₁B, he₁inc⟩ := crr_LRAdj_exists_cutEdge_incident omega n hf₁ hfg₁
  obtain ⟨e₂, he₂B, he₂inc⟩ := crr_LRAdj_exists_cutEdge_incident omega n hf₂ hfg₂
  have hBne : B.Nonempty := ⟨e₁, he₁B⟩
  have hBeven : Ising.kwg_IsEven (Ising.kwg_dualEnds P) B := by
    exact Ising.kwg_primalCut_isEven P (crr_boxRColour omega n)
  have hBmin : ∀ S : Finset (Ising.kwg_Edge P), S ⊆ B → S.Nonempty →
      Ising.kwg_IsEven (Ising.kwg_dualEnds P) S → S = B := by
    intro S hsub hne heven
    exact crr_boxR_dualEven_subset_eq omega n hnoH S hsub hne heven
  have hC₁out : C₁ ≠ O := by
    intro heq
    have hface := crr_whb_box_component_singleton hf₁ heq
    have hc := congrFun hface 0
    rw [mem_rect] at hf₁
    simp at hc
    omega
  have hC₂out : C₂ ≠ O := by
    intro heq
    have hface := crr_whb_box_component_singleton hf₂ heq
    have hc := congrFun hface 0
    rw [mem_rect] at hf₂
    simp at hc
    omega
  have hdual := Ising.kwg_minimalEvenFinset_nonOuter_reachable
    (Ising.kwg_dualEnds P) B O hBne hBeven hBmin hC₁out hC₂out
    ⟨e₁, he₁B, he₁inc⟩ ⟨e₂, he₂B, he₂inc⟩
  have hmapped := hdual.map (crr_cutFaceHom omega n)
  have hrep₁ : crr_boxFaceRep n C₁ = f₁ := by
    symm
    apply crr_whb_box_component_singleton hf₁
    exact (crr_boxFaceRep_component n C₁).symm
  have hrep₂ : crr_boxFaceRep n C₂ = f₂ := by
    symm
    apply crr_whb_box_component_singleton hf₂
    exact (crr_boxFaceRep_component n C₂).symm
  simpa [crr_cutFaceHom, P, B, Rg, O, C₁, C₂, hrep₁, hrep₂] using hmapped


theorem crr_leftFill_finite (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (crr_leftFill ω n).Finite :=
  (rect_finite 0 n 0 n).subset diff_subset


theorem crr_leftFill_bdEdge_is_leftReach_bdEdge
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {p q : Site 2}
    (hadj : (hypercubicLattice 2).Adj p q)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n)
    (hbd : bdEdge (crr_leftFill ω n) s(p, q)) :
    bdEdge (bcd_leftReach ω n) s(p, q) := by
  rw [bdEdge_mk] at hbd ⊢
  by_cases hpR : p ∈ bac_rightComplement ω n
  · have hpFill : p ∉ crr_leftFill ω n := by simp [crr_leftFill, hpR]
    have hqFill : q ∈ crr_leftFill ω n := by
      by_contra hq
      exact hpFill (hbd.mpr hq)
    have hqR : q ∉ bac_rightComplement ω n := hqFill.2
    have hqL : q ∈ bcd_leftReach ω n := by
      rcases crr_nbr_of_rCorner ω n hpR hadj hqbox with hqL | hqR'
      · exact hqL
      · exact absurd hqR' hqR
    have hpL : p ∉ bcd_leftReach ω n := (bac_rightComplement_mem ω n hpR).2
    simp [hpL, hqL]
  · have hpFill : p ∈ crr_leftFill ω n := ⟨hpbox, hpR⟩
    have hqNotFill : q ∉ crr_leftFill ω n := hbd.mp hpFill
    have hqR : q ∈ bac_rightComplement ω n := by
      by_contra hqR
      exact hqNotFill ⟨hqbox, hqR⟩
    have hpL : p ∈ bcd_leftReach ω n := by
      rcases crr_nbr_of_rCorner ω n hqR hadj.symm hpbox with hpL | hpR'
      · exact hpL
      · exact absurd hpR' hpR
    have hqL : q ∉ bcd_leftReach ω n := (bac_rightComplement_mem ω n hqR).2
    simp [hpL, hqL]


theorem crr_leftFill_faceBoundary_inBox_pmd
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g p q : Site 2}
    (hfg : (faceBoundaryGraph (crr_leftFill ω n)).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    (pmd_boxFaceBarrier ω n).Adj f g := by
  refine ⟨hfg.1, p, q, hshared, ?_, hpbox, hqbox⟩
  obtain ⟨p', q', hpq', hadj'⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  rw [hpq'] at hshared
  rw [Sym2.eq_iff] at hshared
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply crr_leftFill_bdEdge_is_leftReach_bdEdge ω n hadj' hpbox hqbox
    rw [← hpq']
    exact hfg.2
  · apply crr_leftFill_bdEdge_is_leftReach_bdEdge ω n hadj'.symm hpbox hqbox
    rw [Sym2.eq_swap, ← hpq']
    exact hfg.2


theorem crr_LRFaceGraph_adj_leftFill
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g : Site 2}
    (h : (crr_LRFaceGraph omega n).Adj f g) :
    (faceBoundaryGraph (crr_leftFill omega n)).Adj f g := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h.2
  refine ⟨h.1.1, ?_⟩
  have hR := h.1.2
  rw [hpq, bdEdge_mk] at hR ⊢
  simp only [crr_leftFill, Set.mem_diff, hp, hq, true_and]
  tauto


theorem crr_LRFaceGraph_le_pmd
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) :
    crr_LRFaceGraph omega n ≤ pmd_boxFaceBarrier omega n := by
  intro f g h
  obtain ⟨p, q, hpq, hp, hq⟩ := h.2
  exact crr_leftFill_faceBoundary_inBox_pmd omega n
    (crr_LRFaceGraph_adj_leftFill omega n h) hpq hp hq


theorem crr_leftFill_walk_lift (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {u v : Site 2}
    (w : (faceBoundaryGraph (crr_leftFill ω n)).Walk u v)
    (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Reachable u v := by
  refine ⟨w.transfer (pmd_boxFaceBarrier ω n) ?_⟩
  intro e he
  refine e.ind (fun f g hfg => ?_) he
  rw [SimpleGraph.mem_edgeSet]
  obtain ⟨p, q, hpq, hp, hq⟩ := hint f g hfg
  exact crr_leftFill_faceBoundary_inBox_pmd ω n (w.adj_of_mem_edges hfg) hpq hp hq


theorem crr_closedBoundary_select_complementaryArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f₁ f₂ : Site 2}
    (c : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₁)
    (hf₂ : f₂ ∈ c.support)
    (hside :
      (∀ f g : Site 2, s(f, g) ∈ (c.takeUntil f₂ hf₂).edges →
        crc2_IsBoxInteriorEdge n f g) ∨
      (∀ f g : Site 2, s(f, g) ∈ (c.dropUntil f₂ hf₂).edges →
        crc2_IsBoxInteriorEdge n f g)) :
    ∃ w : (faceBoundaryGraph (crr_leftFill ω n)).Walk f₁ f₂,
      ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g := by
  rcases hside with htake | hdrop
  · exact ⟨c.takeUntil f₂ hf₂, htake⟩
  · refine ⟨(c.dropUntil f₂ hf₂).reverse, ?_⟩
    intro f g hfg
    apply hdrop f g
    simpa [SimpleGraph.Walk.edges_reverse] using hfg


end Universality
end StatMech

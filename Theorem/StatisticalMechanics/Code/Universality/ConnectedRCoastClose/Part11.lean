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
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part11
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_leftFillInteriorArc_of_frameArcOrder
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (horder : crr_LeftFillFrameArcOrder ω n) : crr_LeftFillInteriorArc ω n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨c, hf₂c, hside⟩ := horder f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  exact crr_closedBoundary_select_complementaryArc ω n c hf₂c hside


theorem crr_interfaceCoastConnected_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (harc : crr_LeftFillInteriorArc ω n) : crr_InterfaceCoastConnected ω n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨w, hw⟩ := harc f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  exact crr_leftFill_walk_lift ω n w hw


theorem crr_interfaceCoastConnected_of_frameArcOrder
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (horder : crr_LeftFillFrameArcOrder ω n) : crr_InterfaceCoastConnected ω n :=
  crr_interfaceCoastConnected_of_leftFillInteriorArc ω n
    (crr_leftFillInteriorArc_of_frameArcOrder ω n horder)


theorem crr_leftFillInteriorArc
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_LeftFillInteriorArc omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ _h1 _h2 _hreach
  obtain ⟨u₁, hu₁, hfu₁, hinc₁⟩ := crr_interfaceSide_reaches_interior omega n hf₁
  obtain ⟨u₂, hu₂, hfu₂, hinc₂⟩ := crr_interfaceSide_reaches_interior omega n hf₂
  have huv := crr_interior_LRFaceGraph_reachable omega n hnoH hu₁ hu₂ hinc₁ hinc₂
  have hLR : (crr_LRFaceGraph omega n).Reachable f₁ f₂ :=
    hfu₁.trans (huv.trans hfu₂.symm)
  obtain ⟨w⟩ := hLR
  let wf : (faceBoundaryGraph (crr_leftFill omega n)).Walk f₁ f₂ :=
    w.transfer _ (fun e he => e.ind (fun f g hfg => by
      rw [SimpleGraph.mem_edgeSet]
      exact crr_LRFaceGraph_adj_leftFill omega n (w.adj_of_mem_edges hfg)) he)
  refine ⟨wf, ?_⟩
  intro f g hfg
  have hfg' : s(f, g) ∈ w.edges := by simpa [wf] using hfg
  exact (w.adj_of_mem_edges hfg').2


theorem crr_leftFillFrameArcOrder
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_LeftFillFrameArcOrder omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  obtain ⟨w, hw⟩ := crr_leftFillInteriorArc omega n hnoH
    f₁ f₂ q₁ q₂ hf₁ hf₂ h1 h2 hreach
  let c : (faceBoundaryGraph (crr_leftFill omega n)).Walk f₁ f₁ := w.append w.reverse
  have hf₂c : f₂ ∈ c.support :=
    w.subset_support_append_left w.reverse w.end_mem_support
  refine ⟨c, hf₂c, Or.inl ?_⟩
  intro f g hfg
  apply hw f g
  have hfgc : s(f, g) ∈ c.edges := c.edges_takeUntil_subset hf₂c hfg
  simpa [c, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse] using hfgc


theorem crr_interfaceCoastConnected
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (hnoH : ¬ HorizontalCrossing omega 0 n 0 n) :
    crr_InterfaceCoastConnected omega n := by
  intro f₁ f₂ q₁ q₂ hf₁ hf₂ _h1 _h2 _hreach
  obtain ⟨u₁, hu₁, hfu₁, hinc₁⟩ := crr_interfaceSide_reaches_interior omega n hf₁
  obtain ⟨u₂, hu₂, hfu₂, hinc₂⟩ := crr_interfaceSide_reaches_interior omega n hf₂
  have huv := crr_interior_LRFaceGraph_reachable omega n hnoH hu₁ hu₂ hinc₁ hinc₂
  exact hfu₁.trans (huv.trans hfu₂.symm) |>.mono (crr_LRFaceGraph_le_pmd omega n)


theorem crr_barrierConnectsRows_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (harc : crr_LeftFillInteriorArc ω n) : pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crr_reachesBottom_of_residue ω n hn hnoH
      (crr_interfaceCoastConnected_of_leftFillInteriorArc ω n harc))


theorem crr_barrierConnectsRows
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    pmd_BarrierConnectsRows ω n :=
  ccc_barrierConnectsRows_of_reachesBottom ω n hn hnoH
    (crr_reachesBottom_of_residue ω n hn hnoH
      (crr_interfaceCoastConnected ω n hnoH))


theorem crr_barrierFace_mem_faceRect
    (ω : ConfigSpace (Sym2 (Site 2))) (n a b : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (h : ∃ g : Site 2, (pmd_boxFaceBarrier ω n).Adj ![a, b] g) :
    (![a, b] : Site 2) ∈ rect 0 (n - 1) (-1) n := by
  obtain ⟨u, v, hsides, hbd, hu, hv⟩ := crr_face_barrier_side ω n a b h
  rw [mem_rect]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rcases hsides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    have ha0 : a ≠ 0 := by
      intro ha
      have huL : (![a, b] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hu, by simpa using ha⟩
      have hvL : (![a, b + 1] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact (hbd.mp huL) hvL
    have han : a ≠ n := by
      intro ha
      have huR : (![a, b] : Site 2) ∉ bcd_leftReach ω n :=
        jex_rightSide_notin_leftReach ω n hnoH ⟨hu, by simpa using ha⟩
      have hvR : (![a, b + 1] : Site 2) ∉ bcd_leftReach ω n :=
        jex_rightSide_notin_leftReach ω n hnoH ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact huR (hbd.mpr hvR)
    omega
  · rw [mem_rect] at hu hv
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
    have ha0 : a + 1 ≠ 0 := by
      intro ha
      have huL : (![a + 1, b] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hu, by simpa using ha⟩
      have hvL : (![a + 1, b + 1] : Site 2) ∈ bcd_leftReach ω n :=
        jex_leftSide_subset_leftReach ω n ⟨hv, by simpa using ha⟩
      rw [bdEdge_mk] at hbd
      exact (hbd.mp huL) hvL
    omega


theorem crr_verticalCrossing_of_barrierConnectsRows
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hrows : pmd_BarrierConnectsRows ω n) :
    VerticalCrossing (fci_faceDualConfig ω) 0 (n - 1) (-1) n := by
  obtain ⟨a₀, a₁, ha0, ha0', ha1, ha1', hreach⟩ := hrows
  obtain ⟨w⟩ := hreach
  have hne : (![a₀, -1] : Site 2) ≠ ![a₁, n] := by
    intro heq
    have hcoord := congrFun heq 1
    have hminus : (-1 : ℤ) = n := by simpa using hcoord
    omega
  have hnonnil : ¬ w.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  let wopen : (openSubgraph 2 (fci_faceDualConfig ω)).Walk ![a₀, -1] ![a₁, n] :=
    w.transfer (openSubgraph 2 (fci_faceDualConfig ω)) (by
      intro e he
      refine e.ind (fun f g hfg => ?_) he
      rw [SimpleGraph.mem_edgeSet]
      have hopen := pmd_boxFaceBarrier_le_faceOpenDual ω n (w.adj_of_mem_edges hfg)
      rwa [fci_faceOpenDual_eq_openSubgraph] at hopen)
  have hsupport : ∀ z ∈ wopen.support, z ∈ rect 0 (n - 1) (-1) n := by
    intro z hz
    have hz' : z ∈ w.support := by simpa [wopen] using hz
    rw [w.mem_support_iff_exists_mem_edges_of_not_nil hnonnil] at hz'
    obtain ⟨e, he, hze⟩ := hz'
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hfg : (pmd_boxFaceBarrier ω n).Adj x y := w.adj_of_mem_edges he
      simp only [Sym2.mem_iff] at hze
      rcases hze with hzx | hzy
      · rw [hzx]
        let a := x 0
        let b := x 1
        have hfeq : x = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
        rw [hfeq]
        exact crr_barrierFace_mem_faceRect ω n a b hnoH ⟨y, by rwa [← hfeq]⟩
      · rw [hzy]
        let a := y 0
        let b := y 1
        have hgeq : y = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
        rw [hgeq]
        exact crr_barrierFace_mem_faceRect ω n a b hnoH ⟨x, by
          rw [← hgeq]
          exact hfg.symm⟩
  have hbot : (![a₀, -1] : Site 2) ∈ rect 0 (n - 1) (-1) n :=
    hsupport _ wopen.start_mem_support
  have htop : (![a₁, n] : Site 2) ∈ rect 0 (n - 1) (-1) n :=
    hsupport _ wopen.end_mem_support
  refine ⟨⟨![a₀, -1], hbot, by simp⟩, ⟨![a₁, n], htop, by simp⟩, ?_⟩
  exact walk_induce_reachable (openSubgraph 2 (fci_faceDualConfig ω))
    (rect 0 (n - 1) (-1) n) wopen hsupport hbot htop


theorem crr_horizontalCrossing_faceBand_subset (n : ℤ) (hn : 0 < n) :
    horizontalCrossingEvent 0 (n + 1) 0 (n - 1) ⊆
      horizontalCrossingEvent 0 (n + 1) 0 n := by
  intro eta heta
  obtain ⟨x, y, hxy⟩ := heta
  have hsub : rect 0 (n + 1) 0 (n - 1) ⊆ rect 0 (n + 1) 0 n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hx : (x : Site 2) ∈ rect 0 (n + 1) 0 n := hsub (leftSide_subset x.2)
  have hy : (y : Site 2) ∈ rect 0 (n + 1) 0 n := hsub (rightSide_subset y.2)
  refine ⟨⟨x, hx, x.2.2⟩, ⟨y, hy, y.2.2⟩, ?_⟩
  exact StatMech.RSW.Strip.connectedWithin_mono_set eta hsub hxy


end Universality
end StatMech

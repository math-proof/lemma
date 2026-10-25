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
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part8
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_mem_LRComponentEdges_iff
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) (f : Site 2)
    (e : Ising.kwg_Edge (crr_boxPlanar n)) :
    e ∈ crr_LRComponentEdges omega n f ↔
      e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
        (crr_boxRColour omega n) ∧
      (crr_LRFaceGraph omega n).Reachable f
        (Ising.kwg_flankLeft (crr_boxPlanar n) e) := by
  classical
  simp [crr_LRComponentEdges]


theorem crr_boxImage_edge_endpoint_mem {n : Int} {e : Sym2 (Site 2)}
    (he : e ∈ (imageGraph (crr_boxPlanar n)).edgeSet) {z : Site 2} (hz : z ∈ e) :
    z ∈ rect 0 n 0 n := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      have hpq : (imageGraph (crr_boxPlanar n)).Adj p q :=
        (SimpleGraph.mem_edgeSet (imageGraph (crr_boxPlanar n))).mp he
      rw [imageGraph_adj] at hpq
      obtain ⟨x, y, _hxy, hxp, hyq⟩ := hpq
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · rw [← hxp]
        exact x.2
      · rw [← hyq]
        exact y.2


theorem crr_face_interior_or_frame {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (h : crc2_IsBoxInteriorEdge n f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨
      f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [hfeq, mem_rect] at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega


theorem crr_boxEdge_one_flank_interior {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (h : crc2_IsBoxInteriorEdge n f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    omega

theorem crr_whb_box_adj_leftLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 0 = -1) (hg : g 0 = -1) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · rw [hfeq, sharedPrimalEdge_top] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner01 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner01, Matrix.cons_val_zero] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_bottom] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner00 a b) (faceCorner10 a b))
    rw [mem_rect] at hz
    simp only [faceCorner00, Matrix.cons_val_zero] at hz
    omega

theorem crr_whb_box_adj_rightLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 0 = n) (hg : g 0 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · simp only [Matrix.cons_val_zero] at hf hg; omega
  · rw [hfeq, sharedPrimalEdge_top] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner01 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner11, Matrix.cons_val_zero] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_bottom] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner00 a b) (faceCorner10 a b))
    rw [mem_rect] at hz
    simp only [faceCorner10, Matrix.cons_val_zero] at hz
    omega

theorem crr_whb_box_adj_bottomLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 1 = -1) (hg : g 1 = -1) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hbline : b = -1 := by simpa [b] using hf
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · rw [hfeq, sharedPrimalEdge_right] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner10 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner10, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_left] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_left (faceCorner00 a b) (faceCorner01 a b))
    rw [mem_rect] at hz
    simp only [faceCorner00, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega

theorem crr_whb_box_adj_topLine {n : Int} {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) (hf : f 1 = n) (hg : g 1 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  refine ⟨hfg, ?_⟩
  intro he
  let a := f 0
  let b := f 1
  have hbline : b = n := by simpa [b] using hf
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg) with rfl | rfl | rfl | rfl
  · rw [hfeq, sharedPrimalEdge_right] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner10 a b) (faceCorner11 a b))
    rw [mem_rect] at hz
    simp only [faceCorner11, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · rw [hfeq, sharedPrimalEdge_left] at he
    have hz := crr_boxImage_edge_endpoint_mem he
      (Sym2.mem_mk_right (faceCorner00 a b) (faceCorner01 a b))
    rw [mem_rect] at hz
    simp only [faceCorner01, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hz
    omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hg; omega


theorem crr_frame_reachable_outerBeacon (n : Int) {f : Site 2}
    (hf : f 0 = -1 ∨ f 0 = n ∨ f 1 = -1 ∨ f 1 = n) :
    (whb_faceRegion (imageGraph (crr_boxPlanar n))).Reachable f ![-1, -1] := by
  classical
  let H := whb_faceRegion (imageGraph (crr_boxPlanar n))
  have leftRun : ∀ y0 y1 : Int, H.Reachable (![-1, y0] : Site 2) ![-1, y1] := by
    intro y0 y1
    let p := sw_vertSeg (-1) y0 y1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_vertSeg (-1) y0 y1).fst_mem_support_of_mem_edges he
      have hv := (sw_vertSeg (-1) y0 y1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_vertSeg_mem_support (-1) y0 y1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_vertSeg_mem_support (-1) y0 y1 v).mp hv
      exact crr_whb_box_adj_leftLine
        ((sw_vertSeg (-1) y0 y1).adj_of_mem_edges he) (by simp) (by simp)
  have rightRun : ∀ y0 y1 : Int, H.Reachable (![n, y0] : Site 2) ![n, y1] := by
    intro y0 y1
    let p := sw_vertSeg n y0 y1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_vertSeg n y0 y1).fst_mem_support_of_mem_edges he
      have hv := (sw_vertSeg n y0 y1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_vertSeg_mem_support n y0 y1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_vertSeg_mem_support n y0 y1 v).mp hv
      exact crr_whb_box_adj_rightLine
        ((sw_vertSeg n y0 y1).adj_of_mem_edges he) (by simp) (by simp)
  have bottomRun : ∀ x0 x1 : Int, H.Reachable (![x0, -1] : Site 2) ![x1, -1] := by
    intro x0 x1
    let p := sw_horizSeg (-1) x0 x1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_horizSeg (-1) x0 x1).fst_mem_support_of_mem_edges he
      have hv := (sw_horizSeg (-1) x0 x1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_horizSeg_mem_support (-1) x0 x1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_horizSeg_mem_support (-1) x0 x1 v).mp hv
      exact crr_whb_box_adj_bottomLine
        ((sw_horizSeg (-1) x0 x1).adj_of_mem_edges he) (by simp) (by simp)
  have topRun : ∀ x0 x1 : Int, H.Reachable (![x0, n] : Site 2) ![x1, n] := by
    intro x0 x1
    let p := sw_horizSeg n x0 x1
    refine ⟨p.transfer H ?_⟩
    intro e he
    induction e with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet]
      have hu := (sw_horizSeg n x0 x1).fst_mem_support_of_mem_edges he
      have hv := (sw_horizSeg n x0 x1).snd_mem_support_of_mem_edges he
      obtain ⟨tu, _htu, rfl⟩ := (sw_horizSeg_mem_support n x0 x1 u).mp hu
      obtain ⟨tv, _htv, rfl⟩ := (sw_horizSeg_mem_support n x0 x1 v).mp hv
      exact crr_whb_box_adj_topLine
        ((sw_horizSeg n x0 x1).adj_of_mem_edges he) (by simp) (by simp)
  rcases hf with hf | hf | hf | hf
  · have hfeq : f = ![-1, f 1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact leftRun _ _
  · have hfeq : f = ![n, f 1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact (rightRun _ _).trans (bottomRun _ _)
  · have hfeq : f = ![f 0, -1] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact bottomRun _ _
  · have hfeq : f = ![f 0, n] := by funext i; fin_cases i <;> simp [hf]
    rw [hfeq]
    exact (topRun _ _).trans (leftRun _ _)


theorem crr_sharedEdge_mem_boxImage {n : Int} {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hp : p ∈ rect 0 n 0 n) (hq : q ∈ rect 0 n 0 n) :
    sharedPrimalEdge f g ∈ (imageGraph (crr_boxPlanar n)).edgeSet := by
  obtain ⟨p', q', hpq', hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg
  rw [hpq'] at hshared ⊢
  rw [Sym2.eq_iff] at hshared
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  rcases hshared with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨p', hp⟩, ⟨q', hq⟩, hpqAdj, rfl, rfl⟩
  · exact ⟨⟨p', hq⟩, ⟨q', hp⟩, hpqAdj, rfl, rfl⟩


theorem crr_whb_box_interior_isolated {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    ¬ (whb_faceRegion (imageGraph (crr_boxPlanar n))).Adj f g := by
  rintro ⟨hfg, hnot⟩
  obtain ⟨p, q, hpq, hp, hq⟩ := crr_faceAdj_isBoxInterior_of_mem_interior hf hfg
  exact hnot (crr_sharedEdge_mem_boxImage hfg hpq hp hq)


theorem crr_whb_box_component_singleton {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hcomp : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f =
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk g) :
    f = g := by
  have hreach := ConnectedComponent.exact hcomp
  obtain ⟨w⟩ := hreach
  cases w with
  | nil => rfl
  | cons hadj _ => exact (crr_whb_box_interior_isolated hf hadj).elim


theorem crr_nonOuter_flank_interior {n : Int}
    (e : Ising.kwg_Edge (crr_boxPlanar n)) {f : Site 2}
    (hf : f = Ising.kwg_flankLeft (crr_boxPlanar n) e ∨
      f = Ising.kwg_flankRight (crr_boxPlanar n) e)
    (houter : (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f ≠
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk ![-1, -1]) :
    f ∈ rect 0 (n - 1) 0 (n - 1) := by
  have hfg := Ising.kwg_flanks_adj (crr_boxPlanar n) e
  have hint : crc2_IsBoxInteriorEdge n
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) := by
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      refine ⟨x.1, y.1, ?_, x.2, y.2⟩
      simpa [Ising.kwg_embeddedEdge, Sym2.map_mk] using
        Ising.kwg_flanks_shared (crr_boxPlanar n) ⟨s(x, y), he⟩
  rcases hf with rfl | rfl
  · rcases crr_face_interior_or_frame hfg hint with hin | hframe
    · exact hin
    · exact (houter (ConnectedComponent.sound
        (crr_frame_reachable_outerBeacon n hframe))).elim
  · have hint' : crc2_IsBoxInteriorEdge n
        (Ising.kwg_flankRight (crr_boxPlanar n) e)
        (Ising.kwg_flankLeft (crr_boxPlanar n) e) := by
      obtain ⟨p, q, hpq, hp, hq⟩ := hint
      refine ⟨p, q, ?_, hp, hq⟩
      calc
        sharedPrimalEdge (Ising.kwg_flankRight (crr_boxPlanar n) e)
            (Ising.kwg_flankLeft (crr_boxPlanar n) e) =
            sharedPrimalEdge (Ising.kwg_flankLeft (crr_boxPlanar n) e)
              (Ising.kwg_flankRight (crr_boxPlanar n) e) :=
          sharedPrimalEdge_comm_of_adj hfg.symm
        _ = s(p, q) := hpq
    rcases crr_face_interior_or_frame hfg.symm hint' with hin | hframe
    · exact hin
    · exact (houter (ConnectedComponent.sound
        (crr_frame_reachable_outerBeacon n hframe))).elim


theorem crr_LRAdj_exists_cutEdge_incident
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g : Site 2}
    (hfint : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hfg : (crr_LRFaceGraph omega n).Adj f g) :
    ∃ e : Ising.kwg_Edge (crr_boxPlanar n),
      e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
        (crr_boxRColour omega n) ∧
      Ising.kwg_incidentMod2
        ((whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f)
        (Ising.kwg_dualEnds (crr_boxPlanar n) e) := by
  classical
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1.1
  obtain ⟨u, v, huv, hu, hv⟩ := hfg.2
  rw [hpq] at huv
  rw [Sym2.eq_iff] at huv
  have hp : p ∈ rect 0 n 0 n ∧ q ∈ rect 0 n 0 n := by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hu, hv⟩
    · exact ⟨hv, hu⟩
  let x : (crr_boxPlanar n).V := ⟨p, hp.1⟩
  let y : (crr_boxPlanar n).V := ⟨q, hp.2⟩
  have hxy : (crr_boxPlanar n).G.Adj x y := hpqAdj
  let e : Ising.kwg_Edge (crr_boxPlanar n) :=
    ⟨s(x, y), (SimpleGraph.mem_edgeSet _).2 hxy⟩
  have hecut : e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n) := by
    rw [Ising.kwg_mem_cutSet]
    change crr_boxRColour omega n x ≠ crr_boxRColour omega n y
    have hbd := hfg.1.2
    rw [hpq, bdEdge_mk] at hbd
    by_cases hpR : p ∈ bac_rightComplement omega n <;>
      by_cases hqR : q ∈ bac_rightComplement omega n <;>
      simp_all [crr_boxRColour, x, y]
  refine ⟨e, hecut, ?_⟩
  have hshared : sharedPrimalEdge
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) = sharedPrimalEdge f g := by
    rw [Ising.kwg_flanks_shared, hpq]
    simp [e, x, y, Ising.kwg_embeddedEdge, Sym2.map_mk]
  have hpairs : s(Ising.kwg_flankLeft (crr_boxPlanar n) e,
      Ising.kwg_flankRight (crr_boxPlanar n) e) = s(f, g) :=
    (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj (crr_boxPlanar n) e) hfg.1.1).mpr hshared
  rw [Sym2.eq_iff] at hpairs
  have hcomp_ne :
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk f ≠
      (whb_faceRegion (imageGraph (crr_boxPlanar n))).connectedComponentMk g := by
    intro heq
    have := crr_whb_box_component_singleton hfint heq
    exact (hypercubicLattice 2).irrefl (this ▸ hfg.1.1)
  rcases hpairs with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · unfold Ising.kwg_dualEnds
    rw [hL, hR]
    exact (Ising.kwg_incidentMod2_mk _ _ _).2 (Or.inl ⟨rfl, hcomp_ne.symm⟩)
  · unfold Ising.kwg_dualEnds
    rw [hL, hR]
    exact (Ising.kwg_incidentMod2_mk _ _ _).2 (Or.inr ⟨rfl, hcomp_ne.symm⟩)

theorem crr_LRAdj_has_interior_endpoint {omega : ConfigSpace (Sym2 (Site 2))} {n : Int}
    {f g : Site 2} (hfg : (crr_LRFaceGraph omega n).Adj f g) :
    f ∈ rect 0 (n - 1) 0 (n - 1) ∨ g ∈ rect 0 (n - 1) 0 (n - 1) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hfg.2
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by funext i; fin_cases i <;> simp [a, b]
  have endpoints : ∀ u v : Site 2, sharedPrimalEdge f g = s(u, v) →
      u ∈ rect 0 n 0 n ∧ v ∈ rect 0 n 0 n := by
    intro u v huv
    rw [huv] at hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩
  rcases crr_face_nbr_cases a b g (hfeq ▸ hfg.1.1) with rfl | rfl | rfl | rfl
  · have he := endpoints (faceCorner10 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_right])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner10, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner01 a b) (by
      rw [hfeq, sharedPrimalEdge_left])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner01, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner01 a b) (faceCorner11 a b) (by
      rw [hfeq, sharedPrimalEdge_top])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner01, faceCorner11, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · have he := endpoints (faceCorner00 a b) (faceCorner10 a b) (by
      rw [hfeq, sharedPrimalEdge_bottom])
    rw [mem_rect, mem_rect] at he
    simp only [faceCorner00, faceCorner10, Matrix.cons_val_zero, Matrix.cons_val_one] at he
    rw [hfeq, mem_rect, mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega


end Universality
end StatMech

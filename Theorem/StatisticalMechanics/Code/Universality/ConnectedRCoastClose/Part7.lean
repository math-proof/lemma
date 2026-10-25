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
import Instance.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part2
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_faceAdj_isBoxInterior_of_mem_interior {n : Int} {f g : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1))
    (hfg : (hypercubicLattice 2).Adj f g) : crc2_IsBoxInteriorEdge n f g := by
  let a := f 0
  let b := f 1
  have hfeq : f = ![a, b] := by
    funext i
    fin_cases i <;> simp [a, b]
  have hab := mem_rect.mp hf
  rw [hfeq] at hfg
  rcases crr_face_nbr_cases a b g hfg with rfl | rfl | rfl | rfl
  · refine ⟨![a + 1, b], ![a + 1, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_right]
      unfold faceCorner10 faceCorner11
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b], ![a, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_left]
      unfold faceCorner00 faceCorner01
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b + 1], ![a + 1, b + 1], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_top]
      unfold faceCorner01 faceCorner11
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
  · refine ⟨![a, b], ![a + 1, b], ?_, ?_, ?_⟩
    · rw [hfeq, sharedPrimalEdge_bottom]
      unfold faceCorner00 faceCorner10
      rfl
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    · rw [mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega


theorem crr_LRFaceGraph_degree_eq_faceBoundary_degree
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    (crr_LRFaceGraph omega n).degree f =
      (faceBoundaryGraph (bac_rightComplement omega n)).degree f := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext g
  simp only [SimpleGraph.mem_neighborFinset]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, crr_faceAdj_isBoxInterior_of_mem_interior hf h.1⟩


theorem crr_LRFaceGraph_degree_even_of_interior
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f : Site 2}
    (hf : f ∈ rect 0 (n - 1) 0 (n - 1)) :
    Even ((crr_LRFaceGraph omega n).degree f) := by
  rw [crr_LRFaceGraph_degree_eq_faceBoundary_degree omega n hf]
  exact degree_faceBoundaryGraph_even (bac_rightComplement omega n) f


theorem crr_LRFaceGraph_adj_of_shared
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(p, q))
    (hpL : p ∈ bcd_leftReach omega n)
    (hqR : q ∈ bac_rightComplement omega n)
    (hpbox : p ∈ rect 0 n 0 n) (hqbox : q ∈ rect 0 n 0 n) :
    (crr_LRFaceGraph omega n).Adj f g := by
  refine ⟨⟨hfg, ?_⟩, p, q, hshared, hpbox, hqbox⟩
  rw [hshared, bdEdge_mk]
  have hpR : p ∉ bac_rightComplement omega n := fun hpR =>
    (bac_rightComplement_mem omega n hpR).2 hpL
  simp [hpR, hqR]


theorem crr_interfaceSideWith_LRNeighbor
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int) {f q : Site 2}
    (h : crr_InterfaceSideWith omega n f q) :
    ∃ g : Site 2, (crr_LRFaceGraph omega n).Adj f g := by
  obtain ⟨hqR, pL, hpL, hadj, hpLbox, hqbox, hpLc, hqc⟩ := h
  set a := f 0 with ha
  set b := f 1 with hb
  have hfe : f = ![a, b] := by funext i; fin_cases i <;> simp [ha, hb]
  rcases hpLc with rfl | rfl | rfl | rfl <;> rcases hqc with rfl | rfl | rfl | rfl <;>
    solve
      | (exfalso; revert hadj; rw [hypercubicLattice_adj, Fin.sum_univ_two];
         simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega)
      | (rw [hfe]; refine ⟨![a, b - 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_bottom,
            faceCorner00, faceCorner10])
      | (rw [hfe]; refine ⟨![a, b - 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_bottom,
            faceCorner00, faceCorner10, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a, b + 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_top,
            faceCorner01, faceCorner11])
      | (rw [hfe]; refine ⟨![a, b + 1], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_top,
            faceCorner01, faceCorner11, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a - 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_left,
            faceCorner00, faceCorner01])
      | (rw [hfe]; refine ⟨![a - 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_left,
            faceCorner00, faceCorner01, Sym2.eq_swap])
      | (rw [hfe]; refine ⟨![a + 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_right,
            faceCorner10, faceCorner11])
      | (rw [hfe]; refine ⟨![a + 1, b], crr_LRFaceGraph_adj_of_shared omega n ?_ ?_
          hpL hqR hpLbox hqbox⟩ <;>
          simp [hypercubicLattice_adj, Fin.sum_univ_two, sharedPrimalEdge_right,
            faceCorner10, faceCorner11, Sym2.eq_swap])


theorem crr_cutEdge_flanks_LRAdj
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Int)
    (e : Ising.kwg_Edge (crr_boxPlanar n))
    (he : e ∈ Ising.kwg_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
      (crr_boxRColour omega n)) :
    (crr_LRFaceGraph omega n).Adj
      (Ising.kwg_flankLeft (crr_boxPlanar n) e)
      (Ising.kwg_flankRight (crr_boxPlanar n) e) := by
  classical
  rcases e with ⟨e, hedge⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : (crr_boxPlanar n).G.Adj x y :=
        (SimpleGraph.mem_edgeSet (crr_boxPlanar n).G).mp hedge
      have hxyLat : (hypercubicLattice 2).Adj (x : Site 2) (y : Site 2) := hxy
      have hsplit : crr_boxRColour omega n x ≠ crr_boxRColour omega n y := by
        simpa [Ising.kwg_primalEnds] using
          (Ising.kwg_mem_cutSet (Ising.kwg_primalEnds (crr_boxPlanar n))
            (crr_boxRColour omega n) ⟨s(x, y), hedge⟩).mp he
      have hshared : sharedPrimalEdge
          (Ising.kwg_flankLeft (crr_boxPlanar n) ⟨s(x, y), hedge⟩)
          (Ising.kwg_flankRight (crr_boxPlanar n) ⟨s(x, y), hedge⟩) =
          s((x : Site 2), (y : Site 2)) := by
        simpa [Ising.kwg_embeddedEdge, Sym2.map_mk] using
          Ising.kwg_flanks_shared (crr_boxPlanar n) ⟨s(x, y), hedge⟩
      have hflank := Ising.kwg_flanks_adj (crr_boxPlanar n) ⟨s(x, y), hedge⟩
      by_cases hxR : (x : Site 2) ∈ bac_rightComplement omega n
      · have hyNotR : (y : Site 2) ∉ bac_rightComplement omega n := by
          intro hyR
          apply hsplit
          simp [crr_boxRColour, hxR, hyR]
        have hyL : (y : Site 2) ∈ bcd_leftReach omega n := by
          rcases crr_nbr_of_rCorner omega n hxR hxyLat y.2 with hyL | hyR
          · exact hyL
          · exact absurd hyR hyNotR
        exact crr_LRFaceGraph_adj_of_shared omega n hflank
          (hshared.trans Sym2.eq_swap) hyL hxR y.2 x.2
      · have hyR : (y : Site 2) ∈ bac_rightComplement omega n := by
          by_contra hyNotR
          apply hsplit
          simp [crr_boxRColour, hxR, hyNotR]
        have hxL : (x : Site 2) ∈ bcd_leftReach omega n := by
          rcases crr_nbr_of_rCorner omega n hyR hxyLat.symm x.2 with hxL | hxR'
          · exact hxL
          · exact absurd hxR' hxR
        exact crr_LRFaceGraph_adj_of_shared omega n hflank hshared hxL hyR x.2 y.2


end Universality
end StatMech

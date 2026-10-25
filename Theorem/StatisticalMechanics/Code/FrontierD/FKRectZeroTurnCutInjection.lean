/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectPathDisplacement_row_eq_sum
    (l : List (Fin 4)) :
    (ons_pathDisplacement l).1 - (ons_pathDisplacement l).2 =
      (l.map fun k => (stepOf k).1 - (stepOf k).2).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [ons_pathDisplacement, List.map_cons, List.sum_cons,
      Prod.fst_add, Prod.snd_add]
    linear_combination ih

theorem fkRectRefinedBoundaryCanonicalCenter_row
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    (fkRectRefinedBoundaryCanonicalCenter R d).1 -
        (fkRectRefinedBoundaryCanonicalCenter R d).2 =
      4 * (d.1.2.val : Int) - 2 := by
  let e := fkRectTorusMedialEdgeEquiv R d.1
  have hdrow : d.1.2 = e.2.2 := by
    rw [← fkRectTorusMedialEdgeEquiv_symm_snd R e]
    simp [e]
  unfold fkRectRefinedBoundaryCanonicalCenter
  rw [show fkRectTorusMedialEdgeEquiv R d.1 = e from rfl, hdrow]
  rcases e with ⟨b, x, y⟩
  cases b <;> by_cases hy : Even y.val <;>
    simp [fkRectRefinedPrimalEdgeCenter, fkRectLiftedIndexedEdgeEnds,
      fkRectSquareDevelopPoint, hy] <;> omega

theorem fkRectBlackDartShiftedPoint_zero_row
    (R : FKRectTorus) (d : FKMedialBlackDart R.medialTorus) :
    (fkRectBlackDartShiftedPoint R (0, 0) d).1 -
        (fkRectBlackDartShiftedPoint R (0, 0) d).2 =
      4 * (d.1.1.2.val : Int) - 2 +
        ((fkRectRefinedSideOffset d.1.2).1 -
          (fkRectRefinedSideOffset d.1.2).2) := by
  unfold fkRectBlackDartShiftedPoint fkRectRefinedDartPoint
  simp only [fkRectSquareDeckTranslation, mul_zero, add_zero,
    Prod.fst, Prod.snd]
  have hcenter := fkRectRefinedBoundaryCanonicalCenter_row R d.1
  omega


theorem fkRectBlackBoundaryStep_row_eq_potential_sub_of_avoidsSeam
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKMedialLoop R.medialTorus
      (fkRectConfigurationToMedialPairing R omega))
    (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
    (d : FKMedialBlackDart R.medialTorus)
    (hdC : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        d.1 = C) :
    2 * ((stepOf (fkMedialStrandDirection
      (fkRectConfigurationToMedialPairing R omega) d.1)).1 -
        (stepOf (fkMedialStrandDirection
          (fkRectConfigurationToMedialPairing R omega) d.1)).2) =
      ((fkRectBlackDartShiftedPoint R (0, 0)
          (fkMedialBlackBoundaryPerm
            (fkRectConfigurationToMedialPairing R omega) d)).1 -
        (fkRectBlackDartShiftedPoint R (0, 0)
          (fkMedialBlackBoundaryPerm
            (fkRectConfigurationToMedialPairing R omega) d)).2) -
      ((fkRectBlackDartShiftedPoint R (0, 0) d).1 -
        (fkRectBlackDartShiftedPoint R (0, 0) d).2) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      d.1 = C at hdC
  change 2 * ((stepOf (fkMedialStrandDirection pairing d.1)).1 -
      (stepOf (fkMedialStrandDirection pairing d.1)).2) = _
  rw [fkRectBlackDartShiftedPoint_zero_row,
    fkRectBlackDartShiftedPoint_zero_row]
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals simp only [fkMedialBlackBoundaryPerm_val,
    fkMedialLocalMate, fkMedialBondMate, pairing, hp,
    fkMedialStrandDirection, fkRectRefinedSideOffset, stepOf,
    Prod.fst, Prod.snd]
  all_goals try rw [finitePeriodicSucc_val R.medialTorus.height_pos]
  all_goals try rw [fkRectCyclicPred_val R.medialTorus.height_pos]
  all_goals try split
  all_goals try omega
  all_goals exfalso
  all_goals
    apply havoid
    refine ⟨i, ?_⟩
    rw [← hdC]
    change (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
        (fkMedialVerticalSeamDart R.medialTorus i) = _
  case false.west.isTrue =>
    have hj : j = svFinLast R.medialTorus.height_pos := by
      ext
      simp [svFinLast]
      omega
    subst j
    rw [show fkMedialVerticalSeamDart R.medialTorus i =
        fkMedialLocalMate pairing
          ((i, svFinLast R.medialTorus.height_pos), .west) by
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, hp]]
    simpa using connectedComponentMk_localMate pairing
      ((i, svFinLast R.medialTorus.height_pos), .west)
  case true.east.isTrue =>
    have hj : j = svFinLast R.medialTorus.height_pos := by
      ext
      simp [svFinLast]
      omega
    subst j
    rw [show fkMedialVerticalSeamDart R.medialTorus i =
        fkMedialLocalMate pairing
          ((i, svFinLast R.medialTorus.height_pos), .east) by
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, hp]]
    simpa using connectedComponentMk_localMate pairing
      ((i, svFinLast R.medialTorus.height_pos), .east)
  case false.east.isTrue =>
    have hj : j = (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height) := by ext; omega
    subst j
    apply SimpleGraph.ConnectedComponent.sound
    convert (fkMedialBoundaryStep_reachable pairing
      ((i, (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height)), .east)).symm using 1
    simp [fkMedialVerticalSeamDart, fkMedialBoundaryStep_apply,
      fkMedialLocalMate, fkMedialBondMate, hp, svCyclicPred_zero]
  case true.west.isTrue =>
    have hj : j = (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height) := by ext; omega
    subst j
    apply SimpleGraph.ConnectedComponent.sound
    convert (fkMedialBoundaryStep_reachable pairing
      ((i, (⟨0, R.medialTorus.height_pos⟩ :
        Fin R.medialTorus.height)), .west)).symm using 1
    simp [fkMedialVerticalSeamDart, fkMedialBoundaryStep_apply,
      fkMedialLocalMate, fkMedialBondMate, hp, svCyclicPred_zero]

theorem fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectHorizontalCutEdges R) :
    fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectHorizontalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  change y.val = 0 at ha
  have hlast : R.height - 1 + 1 = R.height := by omega
  cases b
  · by_cases hy : Even y.val <;>
      simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
        hy, if_true, fkRectCrossesVerticalSeam_mk]
    all_goals rw [fkRectCyclicPred_val]
    all_goals simp only [ha, if_true]
    all_goals exact Or.inl ⟨True.intro, hlast⟩
  · simp only [fkRectTorusIndexedEdge, if_true,
      fkRectCrossesVerticalSeam_mk]
    rw [fkRectCyclicPred_val]
    simp only [ha, if_true]
    exact Or.inl ⟨True.intro, hlast⟩

theorem fkRectCrossesHorizontalSeam_indexedEdge_of_verticalCut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∈ fkRectVerticalCutEdges R) :
    fkRectCrossesHorizontalSeam R (fkRectTorusIndexedEdge R a) := by
  rw [mem_fkRectVerticalCutEdges_iff] at ha
  rcases a with ⟨b, x, y⟩
  rcases ha with ⟨rfl, hx⟩
  change x.val = 0 at hx
  have hlast : R.width - 1 + 1 = R.width := by omega
  by_cases hy : Even y.val <;>
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
      hy, if_true, fkRectCrossesHorizontalSeam_mk]
  all_goals rw [fkRectCyclicPred_val]
  all_goals simp only [hx, if_true]
  all_goals
    first
    | exact Or.inl ⟨True.intro, hlast⟩
    | exact Or.inr ⟨True.intro, hlast⟩

theorem fkRectForceCutClosed_adj_of_not_crossesSeams
    (R : FKRectTorus) (omega : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R omega).Adj x y)
    (hh : ¬ fkRectCrossesHorizontalSeam R s(x, y))
    (hv : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
    (fkRectOpenGraph R (fkRectForceCutClosed R omega)).Adj x y := by
  rcases hxy with ⟨a, hopen, hedge⟩
  refine ⟨a, ?_, hedge⟩
  have hnot : a ∉ fkRectTorusCutEdges R := by
    intro hcut
    rw [fkRectTorusCutEdges, Finset.mem_union] at hcut
    rcases hcut with hcut | hcut
    · apply hv
      rw [← hedge]
      exact fkRectCrossesVerticalSeam_indexedEdge_of_horizontalCut R a hcut
    · apply hh
      rw [← hedge]
      exact fkRectCrossesHorizontalSeam_indexedEdge_of_verticalCut R a hcut
  rw [fkRectForceCutClosed_of_not_mem R omega a hnot, hopen]

end
end StatMech.FrontierD

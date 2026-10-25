/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part3
import Def.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

theorem face_site_eq_of_coords {x y : Site 2}
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext k
  fin_cases k <;> assumption


theorem triHexBrickInner_faceRegion_adj_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (f g : Site 2)
    (hf : f = hexagonalBrickFaceLeft t.1 ∨
      f = hexagonalBrickFaceRight t.1) :
    (whb_faceRegion (imageGraph (triHexPlanarFiniteStarPlanar m))).Adj f g ↔
      (f = hexagonalBrickFaceLeft t.1 ∧
          g = hexagonalBrickFaceRight t.1) ∨
        (f = hexagonalBrickFaceRight t.1 ∧
          g = hexagonalBrickFaceLeft t.1) := by
  have ht0 : Matrix.vecHead t.1 = t.1 0 := rfl
  have ht1 : Matrix.vecHead (Matrix.vecTail t.1) = t.1 1 := rfl
  constructor
  · intro hfg
    rcases hf with rfl | rfl
    · by_cases hg : g = hexagonalBrickFaceRight t.1
      · exact Or.inl ⟨rfl, hg⟩
      · exfalso
        apply hfg.2
        rcases adj_cases hfg.1.symm with
            ⟨h0, hplus | hminus⟩ | ⟨h1, hplus | hminus⟩
        · have hgtop : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred1 hNm t).1 1 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hplus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred1 hNm t).1 1 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgtop, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred1 hNm t) 1
        · have hgbottom : g = triHexBrickSpokeFlank2
              (triHexBrickInnerPred0 hNm t).1 2 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hminus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank1
                (triHexBrickInnerPred0 hNm t).1 2 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [hgbottom, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred0 hNm t) 2
        · have hgright : g = hexagonalBrickFaceRight t.1 := by
            apply face_site_eq_of_coords <;>
              simp [hexagonalBrickFaceLeft,
                hexagonalBrickFaceRight, ht0, ht1] at h1 hplus ⊢ <;> omega
          exact (hg hgright).elim
        · have hgleft : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred0 hNm t).1 0 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h1 hminus ⊢ <;> omega
          have hL : hexagonalBrickFaceLeft t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred0 hNm t).1 0 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred0,
                hexagonalBrickFaceLeft, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgleft, hL]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred0 hNm t) 0
    · by_cases hg : g = hexagonalBrickFaceLeft t.1
      · exact Or.inr ⟨rfl, hg⟩
      · exfalso
        apply hfg.2
        rcases adj_cases hfg.1.symm with
            ⟨h0, hplus | hminus⟩ | ⟨h1, hplus | hminus⟩
        · have hgtop : g = triHexBrickSpokeFlank1
              (triHexBrickInnerPred1 hNm t).1 2 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank1, triHexBrickInnerPred1,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hplus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank2
                (triHexBrickInnerPred1 hNm t).1 2 := by
            ext k
            fin_cases k <;>
              simp [triHexBrickSpokeFlank2, triHexBrickInnerPred1,
                hexagonalBrickFaceRight, hexagonalStep, ht0, ht1]
          rw [sharedPrimalEdge_comm_of_adj hfg.1, hgtop, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerPred1 hNm t) 2
        · have hgbottom : g = triHexBrickSpokeFlank2 t.1 1 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h0 hminus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank1 t.1 1 := by rfl
          rw [hgbottom, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerCell hNm t) 1
        · have hgright : g = triHexBrickSpokeFlank2 t.1 0 := by
            apply face_site_eq_of_coords <;>
              simp [triHexBrickSpokeFlank2,
                hexagonalBrickFaceLeft, hexagonalBrickFaceRight,
                hexagonalStep, ht0, ht1] at h1 hplus ⊢ <;> omega
          have hR : hexagonalBrickFaceRight t.1 =
              triHexBrickSpokeFlank1 t.1 0 := by rfl
          rw [hgright, hR]
          exact triHexBrickSpokeFlanks_shared_mem_imageGraph m
            (triHexBrickInnerCell hNm t) 0
        · have hgleft : g = hexagonalBrickFaceLeft t.1 := by
            apply face_site_eq_of_coords <;>
              simp [hexagonalBrickFaceLeft,
                hexagonalBrickFaceRight, ht0, ht1] at h1 hminus ⊢ <;> omega
          exact (hg hgleft).elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [whb_faceRegion_adj]
      exact ⟨hexagonalBrickFaces_adj t.1,
        triHexPlanarFiniteStar_middle_not_mem_imageGraph m t.1⟩
    · exact (show
        (whb_faceRegion (imageGraph
          (triHexPlanarFiniteStarPlanar m))).Adj
            (hexagonalBrickFaceLeft t.1)
            (hexagonalBrickFaceRight t.1) from
          (whb_faceRegion_adj _ _ _).2
            ⟨hexagonalBrickFaces_adj t.1,
              triHexPlanarFiniteStar_middle_not_mem_imageGraph m t.1⟩).symm

theorem triHexBrickInner_reachable_preserves
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) {f g : Site 2}
    (hf : f = hexagonalBrickFaceLeft t.1 ∨
      f = hexagonalBrickFaceRight t.1)
    (hfg : (whb_faceRegion
      (imageGraph (triHexPlanarFiniteStarPlanar m))).Reachable f g) :
    g = hexagonalBrickFaceLeft t.1 ∨
      g = hexagonalBrickFaceRight t.1 := by
  rcases hfg with ⟨w⟩
  induction w with
  | nil => exact hf
  | @cons a b c hab w ih =>
      have hb := (triHexBrickInner_faceRegion_adj_iff
        hNm t a b hf).mp hab
      have hb' : b = hexagonalBrickFaceLeft t.1 ∨
          b = hexagonalBrickFaceRight t.1 := by
        rcases hb with ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inr h
        · exact Or.inl h
      exact ih hb'


theorem triHexPlanarFiniteStar_pfdFace_eq_inner_iff
    {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) (f : Site 2) :
    BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar m) f =
        triHexPlanarFiniteStarFace m t.1 ↔
      f = hexagonalBrickFaceLeft t.1 ∨
        f = hexagonalBrickFaceRight t.1 := by
  constructor
  · intro hface
    have hreach : (whb_faceRegion
        (imageGraph (triHexPlanarFiniteStarPlanar m))).Reachable
          (hexagonalBrickFaceLeft t.1) f := by
      exact (ConnectedComponent.eq.mp hface).symm
    exact triHexBrickInner_reachable_preserves hNm t (Or.inl rfl) hreach
  · rintro (rfl | rfl)
    · rfl
    · exact (triHexPlanarFiniteStar_pfdFace_left_eq_right m t.1).symm


end
end StatMech.FK.PeriodicPlanar

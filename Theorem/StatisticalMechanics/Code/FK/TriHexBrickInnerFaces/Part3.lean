/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part3
import Instance.StatisticalMechanics.Code.FK.TriHexBrickInnerFaces.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

theorem triHexSpokeFaces_adj (z : Site 2) (i : Fin 3) :
    triangularGraph.Adj (triHexSpokeFace1 z i)
      (triHexSpokeFace2 z i) := by
  have hz0 : Matrix.vecHead z = z 0 := rfl
  have hz1 : Matrix.vecHead (Matrix.vecTail z) = z 1 := rfl
  rw [triangularGraph_adj]
  unfold triangularAdj
  fin_cases i
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨0, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨1, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]
  · simp only [triHexSpokeFace1, triHexSpokeFace2,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨2, Or.inl ?_⟩
    funext k
    fin_cases k <;> simp [hexagonalStep, triangularStep, hz0, hz1]

theorem triHexBrickFullDual_adj_of_spoke
    {N m : Nat} (hNm : N < m)
    (x y : {z : Site 2 // z ∈ box 2 N})
    (z : TriHexPlanarFiniteCell m) (i : Fin 3)
    (hpair : s(triHexSpokeFace1 z.1 i, triHexSpokeFace2 z.1 i) =
      s(x.1, y.1)) :
    (triHexBrickFullDualGraph m).Adj
      (triHexBrickInnerFaceMap N m x)
      (triHexBrickInnerFaceMap N m y) := by
  rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj]
  refine ⟨fun h => ?_, triHexPlanarFiniteStarEdgeEquiv m (z, i), by simp, ?_⟩
  · have hxy := triHexBrickInnerFaceMap_injective hNm h
    subst y
    rw [Sym2.eq_iff] at hpair
    rcases hpair with hpair | hpair
    · exact (triHexSpokeFaces_adj z.1 i).ne
        (hpair.1.trans hpair.2.symm)
    · exact (triHexSpokeFaces_adj z.1 i).ne
        (hpair.1.trans hpair.2.symm)
  · rw [triHexPlanarFiniteStar_dualEnds]
    simpa [triHexBrickInnerFaceMap] using congrArg
      (Sym2.map (triHexPlanarFiniteStarFace m)) hpair


theorem triHexBrickInnerFaceMap_adj
    {N m : Nat} (hNm : N < m)
    (x y : {z : Site 2 // z ∈ box 2 N}) :
    (triHexBrickInnerTriangleGraph N).Adj x y ↔
      (triHexBrickFullDualGraph m).Adj
        (triHexBrickInnerFaceMap N m x)
        (triHexBrickInnerFaceMap N m y) := by
  have hx0 : Matrix.vecHead x.1 = x.1 0 := rfl
  have hx1 : Matrix.vecHead (Matrix.vecTail x.1) = x.1 1 := rfl
  have hy0 : Matrix.vecHead y.1 = y.1 0 := rfl
  have hy1 : Matrix.vecHead (Matrix.vecTail y.1) = y.1 1 := rfl
  constructor
  · intro hxy
    change triangularGraph.Adj x.1 y.1 at hxy
    rw [triangularGraph_adj] at hxy
    rcases hxy with ⟨i, hpos | hneg⟩
    · fin_cases i
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerCell hNm x) 0
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerCell, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerCell hNm x) 1
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerCell, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
      · apply triHexBrickFullDual_adj_of_spoke hNm x y
          (triHexBrickInnerPred0 hNm x) 2
        apply Sym2.eq_iff.mpr
        left
        constructor <;> apply face_site_eq_of_coords <;>
          simp [triHexSpokeFace1, triHexSpokeFace2,
            triHexBrickInnerPred0, hexagonalStep, triangularStep,
              hx0, hx1, hy0, hy1, funext_iff]
              at hpos ⊢ <;> omega
    · fin_cases i
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerCell hNm y) 0 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerCell, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff] at hneg ⊢ <;>
              omega)).symm
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerCell hNm y) 1 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerCell, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff] at hneg ⊢ <;>
              omega)).symm
      · exact (triHexBrickFullDual_adj_of_spoke hNm y x
          (triHexBrickInnerPred0 hNm y) 2 (by
            apply Sym2.eq_iff.mpr
            left
            constructor <;> apply face_site_eq_of_coords <;>
              simp [triHexSpokeFace1, triHexSpokeFace2,
                triHexBrickInnerPred0, hexagonalStep, triangularStep,
                  hx0, hx1, hy0, hy1, funext_iff]
                  at hneg ⊢ <;> omega)).symm
  · intro hxy
    rw [triHexBrickFullDualGraph, BeffaraDC.pfdClosedDual_adj] at hxy
    obtain ⟨_, e, _, hends⟩ := hxy
    generalize ha : (triHexPlanarFiniteStarEdgeEquiv m).symm e = a
    rcases a with ⟨z, i⟩
    have he := (triHexPlanarFiniteStarEdgeEquiv m).apply_symm_apply e
    rw [ha] at he
    rw [← he, triHexPlanarFiniteStar_dualEnds] at hends
    rw [Sym2.eq_iff] at hends
    change triangularGraph.Adj x.1 y.1
    rcases hends with hends | hends
    · have hx : triHexSpokeFace1 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.1
      have hy : triHexSpokeFace2 z.1 i = y.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.2
      simpa [hx, hy] using triHexSpokeFaces_adj z.1 i
    · have hy : triHexSpokeFace1 z.1 i = y.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm y _).mp hends.1
      have hx : triHexSpokeFace2 z.1 i = x.1 :=
        (triHexPlanarFiniteStarFace_eq_inner_iff hNm x _).mp hends.2
      simpa [hx, hy] using (triHexSpokeFaces_adj z.1 i).symm

end
end StatMech.FK.PeriodicPlanar

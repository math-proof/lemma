/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Def.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part8


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

theorem sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat) :
    (∑ j ∈ Finset.range height, ∑ i ∈ Finset.range width,
      reflectedRadialBilinearCellContour mesh
        (F (i0 + i) (j0 + j))
        (F (i0 + i + 1) (j0 + j))
        (F (i0 + i) (j0 + j + 1))
        (F (i0 + i + 1) (j0 + j + 1))) =
      reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height := by
  let H : Nat -> Nat -> Complex :=
    reflectedRadialHorizontalEdgeIntegral mesh F
  let V : Nat -> Nat -> Complex :=
    reflectedRadialVerticalEdgeIntegral mesh F
  have hrow (j : Nat) :
      (∑ i ∈ Finset.range width,
        reflectedRadialBilinearCellContour mesh
          (F (i0 + i) j) (F (i0 + i + 1) j)
          (F (i0 + i) (j + 1)) (F (i0 + i + 1) (j + 1))) =
        (∑ i ∈ Finset.range width, H (i0 + i) j) +
          V (i0 + width) j -
          (∑ i ∈ Finset.range width, H (i0 + i) (j + 1)) - V i0 j := by
    simp only [reflectedRadialBilinearCellContour_eq_edgeCoboundary,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    change (∑ i ∈ Finset.range width, H (i0 + i) j) +
        (∑ i ∈ Finset.range width, V (i0 + i + 1) j) -
        (∑ i ∈ Finset.range width, H (i0 + i) (j + 1)) -
        (∑ i ∈ Finset.range width, V (i0 + i) j) = _
    have hV := sum_range_add_one_sub (fun i => V i j) i0 width
    have hV' : (∑ i ∈ Finset.range width, V (i0 + i + 1) j) -
        (∑ i ∈ Finset.range width, V (i0 + i) j) =
        V (i0 + width) j - V i0 j := by
      rw [← Finset.sum_sub_distrib]
      exact hV
    linear_combination hV'
  simp only [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hH := sum_range_sub_add_one
    (fun j => ∑ i ∈ Finset.range width, H (i0 + i) j) j0 height
  rw [Finset.sum_sub_distrib] at hH
  unfold reflectedRadialRectangleBoundaryIntegral
  dsimp only [H, V] at hH ⊢
  linear_combination hH


theorem reflectedRadialRectangleBoundaryIntegral_eq_zero_of_cellCR
    (mesh : Real) (F : Nat -> Nat -> Complex)
    (i0 j0 width height : Nat)
    (hCR : forall i j, i < width -> j < height ->
      IsingCellCRAt F (i0 + i) (j0 + j)) :
    reflectedRadialRectangleBoundaryIntegral mesh F i0 j0 width height = 0 := by
  rw [← sum_reflectedRadialBilinearCellContour_eq_rectangleBoundary]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro i hi
  exact reflectedRadialBilinearCellContour_eq_zero_of_cellCR mesh _ _ _ _
    (hCR i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))


end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquarePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingRectanglePrimitiveWithBase_eq_of_local_increments
    (base : Real) (horizontal vertical G : Nat → Nat → Real)
    (width height : Nat)
    (hbase : G 0 0 = base)
    (hhorizontal : ∀ i < width, G (i + 1) 0 - G i 0 = horizontal i 0)
    (hvertical : ∀ i ≤ width, ∀ j < height,
      G i (j + 1) - G i j = vertical i j) :
    ∀ i ≤ width, ∀ j ≤ height,
      G i j = base + isingRectanglePrimitive horizontal vertical i j := by
  have hbottom : ∀ i ≤ width,
      G i 0 = base + ∑ k ∈ Finset.range i, horizontal k 0 := by
    intro i hi
    induction i with
    | zero => simpa using hbase
    | succ i ih =>
        rw [Finset.sum_range_succ]
        have hinc := hhorizontal i (by omega)
        have hprev := ih (by omega)
        linarith
  intro i hi j hj
  induction j with
  | zero =>
      simpa [isingRectanglePrimitive] using hbottom i hi
  | succ j ih =>
      rw [isingRectanglePrimitive, Finset.sum_range_succ]
      have hinc := hvertical i hi j (by omega)
      have hprev := ih (by omega)
      rw [isingRectanglePrimitive] at hprev
      linarith

theorem fkIsingSquareRadialPatchHorizontal_endpoint_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, by omega⟩, ⟨j, hj⟩), heven⟩ := by
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .west by
    simp [fkIsingSquareRadialPatchBottomSide, heven]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, hj⟩
  simp [fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchHorizontal_face_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by
          change ¬ Even ((i + 1) + j)
          rw [Nat.not_even_iff]
          have hmod := Nat.even_iff.mp heven
          omega⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .west by
    simp [fkIsingSquareRadialPatchBottomSide, heven]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  unfold fkIsingSquareWedgeFaceKey fkIsingSquareDartEndpoint
    fkIsingSquareDartDirection
  rw [fkIsingSquareOrientedEdge_directionEdge]
  have hmod := Nat.even_iff.mp heven
  simp [fkIsingSquareDirectionEdgeOrientation,
    fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
    fkIsingSquareRadialPatchVertex, fkIsingSquareSideCorner]
  rw [fkIsingSquareRadialPatchHalf_eq]
  constructor <;> push_cast <;> omega

theorem fkIsingSquareRadialPatchHorizontal_endpoint_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i + 1, hi⟩, ⟨j, hj⟩), by
          change Even ((i + 1) + j)
          rw [Nat.even_iff]
          have hmod := Nat.not_even_iff.mp hodd
          omega⟩ := by
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .north by
    simp [fkIsingSquareRadialPatchBottomSide, hodd]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .north) = _
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
  simp only [fkIsingSquareDartEndpoint_directionEdge_north]
  simp only [fkIsingSquareSideCorner]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩
  change fkIsingSquareNeighbor n
      (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, hj⟩)
        .north _ =
    fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩
  have hmod := Nat.not_even_iff.mp hodd
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq] <;>
    omega

theorem fkIsingSquareRadialPatchHorizontal_face_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i + 1 < m) (hj : j < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchHorizontalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, by omega⟩, ⟨j, hj⟩), hodd⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchHorizontalIncidence_bottom
    n m hn hm hmpos i j (by omega) hj]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchBottomSide i j = .north by
    simp [fkIsingSquareRadialPatchBottomSide, hodd]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩,
        .north) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm _ _ hodd]
  rw [fkIsingSquareRadialPatchHalf_eq]
  simp

theorem fkIsingSquareRadialPatchVertical_endpoint_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (heven : Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, hi⟩, ⟨j, by omega⟩), heven⟩ := by
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .south by
    simp [fkIsingSquareRadialPatchLeftSide, heven]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .south) = _
  rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, by omega⟩
  simp [fkIsingSquareSideCorner]

theorem fkIsingSquareRadialPatchVertical_face_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (heven : Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by
          change ¬ Even (i + (j + 1))
          rw [Nat.not_even_iff]
          have hmod := Nat.even_iff.mp heven
          omega⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .south by
    simp [fkIsingSquareRadialPatchLeftSide, heven]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .south) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_even n m hm _ _ heven]
  rw [fkIsingSquareRadialPatchHalf_eq]
  have hmod := Nat.even_iff.mp heven
  simp
  constructor <;> push_cast <;> omega

theorem fkIsingSquareRadialPatchVertical_endpoint_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchPrimalFullVertex n m hm
        ⟨(⟨i, hi⟩, ⟨j + 1, hj⟩), by
          change Even (i + (j + 1))
          rw [Nat.even_iff]
          have hmod := Nat.not_even_iff.mp hodd
          omega⟩ := by
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialEndpoint_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .west by
    simp [fkIsingSquareRadialPatchLeftSide, hodd]]
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
  simp only [fkIsingSquareDartEndpoint_directionEdge_north]
  simp only [fkIsingSquareSideCorner]
  change _ = fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩
  change fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, by omega⟩ =
    fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩
  have hmod := Nat.not_even_iff.mp hodd
  apply Subtype.ext
  funext k
  fin_cases k <;>
    simp [fkIsingSquareRadialPatchVertex,
      fkIsingSquareRadialPatchHalf_eq] <;>
    omega

theorem fkIsingSquareRadialPatchVertical_face_of_odd
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (i j : Nat) (hi : i < m) (hj : j + 1 < m)
    (hodd : ¬ Even (i + j)) :
    fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquareRadialPatchVerticalIncidence
          n m hn hm hmpos i j) =
      fkIsingSquareRadialPatchDualFullFace n m hm (by omega)
        ⟨(⟨i, hi⟩, ⟨j, by omega⟩), hodd⟩ := by
  apply fkIsingSquareInteriorCellKey_injective n
  rw [fkIsingSquareFullFaceOfRadialIncidence_key,
    fkIsingSquareRadialPatchDualFullFace_key]
  rw [fkIsingSquareRadialPatchVerticalIncidence_left
    n m hn hm hmpos i j hi (by omega)]
  simp only [fkIsingSquareRadialPatchIncidence,
    fkIsingSquareInteriorRadialCellIncidence,
    fkIsingSquareInteriorRadialFaceKey_mk]
  rw [show fkIsingSquareRadialPatchLeftSide i j = .west by
    simp [fkIsingSquareRadialPatchLeftSide, hodd]]
  change fkIsingSquareWedgeFaceKey n
      (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩,
        .west) = _
  rw [fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm _ _ hodd]
  rw [fkIsingSquareRadialPatchHalf_eq]
  simp

end
end StatMech.Universality

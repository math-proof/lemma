/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullVertexCoordinate_sum_even
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Even ((fkIsingSquareFullVertexCoordinate n x).1 +
      (fkIsingSquareFullVertexCoordinate n x).2) := by
  refine ⟨x.1 0, ?_⟩
  simp [fkIsingSquareFullVertexCoordinate]

theorem fkIsingSquareFullFaceCoordinate_sum_not_even
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    ¬ Even ((fkIsingSquareFullFaceCoordinate n c).1 +
      (fkIsingSquareFullFaceCoordinate n c).2) := by
  rintro ⟨k, hk⟩
  simp [fkIsingSquareFullFaceCoordinate] at hk
  omega

theorem fkIsingSquareFull_exists_incidence_of_radiallyAdjacent
    (n : Nat) (hn : 0 < n)
    (x : FKIsingSquareFullVertexNode n)
    (c : FKIsingSquareFullFaceNode n)
    (h : fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1 + (1 : Int),
            (fkIsingSquareFullVertexCoordinate n x).2) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1,
            (fkIsingSquareFullVertexCoordinate n x).2 + (1 : Int)) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1 - (1 : Int),
            (fkIsingSquareFullVertexCoordinate n x).2) ∨
        fkIsingSquareFullFaceCoordinate n c =
          ((fkIsingSquareFullVertexCoordinate n x).1,
            (fkIsingSquareFullVertexCoordinate n x).2 - (1 : Int))) :
    ∃ e : FKIsingSquareInteriorRadialIncidence n hn,
      fkIsingSquareInteriorRadialEndpoint n hn e = x ∧
        fkIsingSquareInteriorRadialFaceKey n hn e =
          fkIsingSquareInteriorCellKey n c := by
  rcases h with h | h | h | h
  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change x.1 0 < (n : Int)
      omega
    let d := fkIsingSquareDirectionDart n x .east heast .counterclockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey

  · have heast : fkIsingSquareDirectionAvailable n x .east := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change x.1 0 < (n : Int)
      omega
    let d := fkIsingSquareDirectionDart n x .east heast .clockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey
  · have hwest : fkIsingSquareDirectionAvailable n x .west := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change -(n : Int) < x.1 0
      omega
    let d := fkIsingSquareDirectionDart n x .west hwest .counterclockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey
  · have hwest : fkIsingSquareDirectionAvailable n x .west := by
      have hc := fkIsingSquareInteriorCellKey_interior n c
      have hx := fkIsingSquareVertex_coordinate_bounds n x 0
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp [fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h0 h1
      simp [fkIsingSquareInteriorFaceKey] at hc
      change -(n : Int) < x.1 0
      omega
    let d := fkIsingSquareDirectionDart n x .west hwest .clockwise
    have hdkey : fkIsingSquareWedgeFaceKey n d =
        fkIsingSquareInteriorCellKey n c := by
      unfold fkIsingSquareWedgeFaceKey
      simp [d, fkIsingSquareFullFaceCoordinate,
        fkIsingSquareFullVertexCoordinate] at h ⊢
      apply Prod.ext <;> omega
    let di : FKIsingSquareInteriorRadialDart n :=
      ⟨d, hdkey.symm ▸ fkIsingSquareInteriorCellKey_interior n c⟩
    refine ⟨Quot.mk _ di, ?_, ?_⟩
    · simp [di, d]
    · simpa [di] using hdkey

end
end StatMech.Universality

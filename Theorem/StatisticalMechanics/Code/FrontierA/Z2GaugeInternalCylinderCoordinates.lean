/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalPlusCorrDecay
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderCoordinates


namespace StatMech.FrontierA

open StatMech StatMech.Lattice

noncomputable section

theorem internalCylinderUpperCell_injective
    (N m : Nat) (hNm : N <= m) :
    Function.Injective (internalCylinderUpperCell N m hNm) := by
  intro ij kl h
  simp only [internalCylinderUpperCell, CubicalCell.mk.injEq] at h
  apply Prod.ext
  · apply Fin.ext
    have hx := congrArg Fin.val h.1
    simp only at hx
    omega
  · apply Fin.ext
    have hy := congrArg Fin.val h.2.1
    simp only at hy
    omega

theorem internalCylinderBoundaryCell_injective
    (N m : Nat) (hN : 0 < N) (hNm : N <= m) :
    Function.Injective (internalCylinderBoundaryCell N m hN hNm) := by
  intro q r h
  simp only [internalCylinderBoundaryCell, CubicalCell.mk.injEq] at h
  rcases q with ⟨qx, qy, qz⟩
  rcases r with ⟨rx, ry, rz⟩
  simp only at h
  rw [CubicalCell.mk.injEq]
  constructor
  · apply Fin.ext
    have hx := congrArg Fin.val h.1
    simp only at hx
    omega
  constructor
  · apply Fin.ext
    have hy := congrArg Fin.val h.2.1
    simp only at hy
    omega
  · apply Fin.ext
    have hz := congrArg Fin.val h.2.2
    simp only at hz
    omega


theorem cubicalInternalCentralUpperVertices_eq_internalCylinderUpperCell
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    cubicalInternalCentralUpperVertices N m hNm =
      (Finset.univ : Finset (internalCylinderUpperIndex N)).image
        (fun ij => some (internalCylinderUpperCell N m hNm ij)) := by
  rw [cubicalInternalCentralUpperVertices_eq_coordinate N m hN hNm]
  unfold cubicalInternalCentralUpperCoordinateVertices
  apply Finset.image_congr
  intro ij hij
  congr 1


theorem oddCubicalCenteredSite_internalCylinderUpperCell
    (N m : Nat) (hNm : N <= m)
    (ij : internalCylinderUpperIndex N) :
    oddCubicalCenteredSite m (internalCylinderUpperCell N m hNm ij) =
      internalCylinderUpperSite ij := by
  funext k
  fin_cases k <;>
    simp [internalCylinderUpperCell, internalCylinderUpperSite]


theorem oddCubicalCenteredSite_internalCylinderBoundaryCell
    (N m : Nat) (hN : 0 < N) (hNm : N <= m)
    (q : CubicalCell N N N) :
    oddCubicalCenteredSite m
        (internalCylinderBoundaryCell N m hN hNm q) =
      internalCylinderBoundarySite q := by
  funext k
  fin_cases k <;>
    simp [internalCylinderBoundaryCell, internalCylinderBoundarySite] <;>
    omega


theorem cubicalInternalCentralBoundaryVertices_eq_coordinate
    (N m : Nat) (hN : 0 < N) (hNm : N ≤ m) :
    cubicalInternalCentralBoundaryVertices N m =
      internalCylinderBoundaryCoordinateVertices N m hN hNm := by
  ext v
  constructor
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    rcases q with ⟨qx, qy, qz⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    let qi : CubicalCell N N N := CubicalCell.mk
      ⟨qx.val - m, by omega⟩
      ⟨qy.val - m, by omega⟩
      ⟨m - 1 - qz.val, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨qi, ?_, ?_⟩
    · simp only [internalCylinderBoundaryIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      dsimp [qi]
      omega
    · congr 1
      rw [CubicalCell.mk.injEq]
      simp only [internalCylinderBoundaryCell, qi]
      constructor
      · apply Fin.ext
        simp only
        omega
      constructor
      · apply Fin.ext
        simp only
        omega
      · apply Fin.ext
        simp only
        omega
  · intro hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    simp only [internalCylinderBoundaryIndices, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq
    apply Finset.mem_image.mpr
    refine ⟨internalCylinderBoundaryCell N m hN hNm q, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      internalCylinderBoundaryCell]
    omega

end
end StatMech.FrontierA

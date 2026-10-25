/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareCenteredRadialPatchEdge_eq_east
    (n : Nat) (i j : Fin (2 * n)) (h : Even (i.1 + j.1)) :
    fkIsingSquareCenteredRadialPatchEdge n i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareCenteredRadialPatchVertex n i j) .east
        (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using
          fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
  unfold fkIsingSquareCenteredRadialPatchEdge
  simp only [fkIsingSquareCenteredRadialPatchDirection, if_pos h]

theorem fkIsingSquareCenteredRadialPatchEdge_eq_north
    (n : Nat) (i j : Fin (2 * n)) (h : ¬ Even (i.1 + j.1)) :
    fkIsingSquareCenteredRadialPatchEdge n i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareCenteredRadialPatchVertex n i j) .north
        (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using
          fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
  unfold fkIsingSquareCenteredRadialPatchEdge
  simp only [fkIsingSquareCenteredRadialPatchDirection, if_neg h]


theorem fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge
    (n m a b : Nat) (hm : m ≤ n) (ha : a < m) (hb : b < m) :
    fkIsingSquareCenteredRadialPatchEdge n
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareRadialPatchEdge n m hm
        ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hhalf : centeredRadialHalf (n + a) (n + b) =
      n + (a + b + 1) / 2 := by
    simp [centeredRadialHalf]
    omega
  have hv : fkIsingSquareCenteredRadialPatchVertex n
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareRadialPatchVertex n m hm ⟨a, ha⟩ ⟨b, hb⟩ := by
    apply Subtype.ext
    funext k
    fin_cases k
    · change ((centeredRadialHalf (n + a) (n + b) : Int) - (n : Int)) =
          ((a + b + 1) / 2 : Int)
      rw [hhalf]
      omega
    · change ((n + a : Nat) : Int) -
          (centeredRadialHalf (n + a) (n + b) : Int) =
        (a : Int) - ((a + b + 1) / 2 : Int)
      rw [hhalf]
      omega
  have heven : Even (n + a + (n + b)) ↔ Even (a + b) := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c - n, ?_⟩
      omega
    · rintro ⟨c, hc⟩
      refine ⟨n + c, ?_⟩
      omega
  have hd : fkIsingSquareCenteredRadialPatchDirection
        (n + a) (n + b) = fkIsingSquareRadialPatchDirection a b := by
    simp [fkIsingSquareCenteredRadialPatchDirection,
      fkIsingSquareRadialPatchDirection, heven]
  unfold fkIsingSquareCenteredRadialPatchEdge fkIsingSquareRadialPatchEdge
  simpa only [hv, hd]


end
end StatMech.Universality

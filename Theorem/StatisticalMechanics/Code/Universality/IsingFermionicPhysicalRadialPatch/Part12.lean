/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open Filter Set Topology

noncomputable section

theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) :
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p) =
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm hmpos p.1.1.1 p.1.2.1 := by
  exact (fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm).extend_apply
    _ _ p

theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (i j : Nat) (hi : i < m) (hj : j < m)
    (heven : Even (i + j)) :
    fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base
        (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩) =
      base + fkIsingSquareRadialPatchPrimitive
        n m hn hm hmpos i j := by
  let p : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨i, hi⟩, ⟨j, hj⟩), heven⟩
  simpa only [p, fkIsingSquareRadialPatchPrimalNodeVertex] using
    fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply
      n m hn hm hmpos base p


theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
  let H := fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
  calc
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchDiagonalLaplacian
        (fun a b ↦ base + H a b) i j := by
          apply fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal
            n m i j hm hi0 hi1 hj0 hj1 heven
          · exact fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
              n m hn hm hmpos base i j (by omega) (by omega) heven
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
          · apply fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even
            rw [Nat.even_iff]
            have hmod := Nat.even_iff.mp heven
            omega
    _ = fkIsingSquareRadialPatchDiagonalLaplacian H i j := by
      unfold fkIsingSquareRadialPatchDiagonalLaplacian
      ring


theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
        (fkIsingSquareRadialPatchPrimalPrimitiveExtension
          n m hn hm hmpos base)
        (fkIsingSquareRadialPatchVertex n m hm
          ⟨i, by omega⟩ ⟨j, by omega⟩) =
      fkIsingSquareRadialPatchPrimalIncrementDivergence
        n m hn hm hmpos i j := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]


theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonneg_of_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j))
    (hquad : IsingSquareSHolomorphicQuad
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)) :
    0 ≤ isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _ hquad


theorem fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareRadialPatchPrimalPrimitiveExtension
        n m hn hm hmpos base)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) ≤ 0 := by
  rw [fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence
      n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven,
    fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian
      n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven]
  apply isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad
  exact fkIsingSquareRadialPatchFullObservable_quad
    n m i j hn hm hi0 hi1 hj0 hj1 heven


end
end StatMech.Universality

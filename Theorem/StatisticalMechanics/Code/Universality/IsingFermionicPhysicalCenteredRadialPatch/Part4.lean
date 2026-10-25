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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingReflectedCenteredRadialGridPosition_eq
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i j =
      (mesh * (((i : Real) + (j : Real) + 1) / 2 - n) : Real) +
        (mesh * (((j : Real) - (i : Real)) / 2) : Real) * Complex.I := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring

theorem isingReflectedCenteredRadialGridPosition_succ_i
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + 1) j =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (mesh : Complex) / 2 * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring

theorem isingReflectedCenteredRadialGridPosition_succ_j
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (mesh : Complex) / 2 * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring


theorem isingReflectedCenteredRadialGridPosition_succ_both
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + 1) (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n i j + mesh := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    isingReflectedCenteredRadialGridPosition_succ_i]
  ring


theorem isingReflectedCenteredRadialGridPosition_vertical_macroStep
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n (i + 1) j +
        mesh * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    isingReflectedCenteredRadialGridPosition_succ_i]
  ring

theorem isingReflectedCenteredRadialGridPosition_diagonal_add
    (mesh : Real) (n i j k : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + k) (j + k) =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (k : Real) * mesh := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast
  ring

theorem isingReflectedCenteredRadialGridPosition_antidiagonal_add
    (mesh : Real) (n i j N k : Nat) (hk : k ≤ N) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + (N - k)) (j + k) =
      isingReflectedCenteredRadialGridPosition mesh n (i + N) j +
        ((k : Real) * mesh) * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hk]
  ring

theorem isingReflectedCenteredRadialGridPosition_diagonal_sub
    (mesh : Real) (n i j N M k : Nat) (hkN : k ≤ N) (hkM : k ≤ M) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + (N - k)) (j + (M - k)) =
      isingReflectedCenteredRadialGridPosition mesh n (i + N) (j + M) -
        (k : Real) * mesh := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hkN, Nat.cast_sub hkM]
  ring

theorem isingReflectedCenteredRadialGridPosition_antidiagonal_sub
    (mesh : Real) (n i j N k : Nat) (hk : k ≤ N) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + k) (j + (N - k)) =
      isingReflectedCenteredRadialGridPosition mesh n i (j + N) -
        ((k : Real) * mesh) * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hk]
  ring


theorem isingCenteredRadialGridPosition_eq_scaledCarrierPosition
    (n : Nat) (hn : 0 < n) (mesh : Real) (i j : Fin (2 * n))
    (s : FKIsingMedialSide) :
    isingCenteredRadialGridPosition mesh n i.1 j.1 =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn
        (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) := by
  unfold isingCenteredRadialGridPosition isingRadialGridPosition
  change _ = (mesh : Complex) *
    ((fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareCenteredRadialPatchEdge n i j)).tail.1 +
      fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareCenteredRadialPatchEdge n i j)).head.1) / 2)
  by_cases h : Even (i.1 + j.1)
  · rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n i j h,
      fkIsingSquareOrientedEdge_directionEdge]
    simp [fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
      Complex.ext_iff]
    have hmod := Nat.even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) := by exact_mod_cast hqNat
    have hreal : ((i.1 : Real) + (j.1 : Real) + 1) / 2 =
        (((i.1 + j.1 + 1) / 2 : Nat) : Real) + 1 / 2 := by
      linarith
    have him : ((i.1 : Real) - (j.1 : Real)) / 2 =
        (i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      linarith
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    constructor
    · rw [hreal]
      rw [hdivReal]
      ring
    · left
      exact him
  · rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n i j h,
      fkIsingSquareOrientedEdge_directionEdge]
    simp [fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
      Complex.ext_iff]
    have hmod := Nat.not_even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 + 1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) + 1 := by exact_mod_cast hqNat
    have hreal : ((i.1 : Real) + (j.1 : Real) + 1) / 2 =
        (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      linarith
    have him : (i.1 : Real) - (j.1 : Real) =
        ((i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real)) +
          ((i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real) + 1) := by
      linarith
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    constructor
    · rw [hreal]
      rw [hdivReal]
      ring
    · left
      exact him


end
end StatMech.Universality

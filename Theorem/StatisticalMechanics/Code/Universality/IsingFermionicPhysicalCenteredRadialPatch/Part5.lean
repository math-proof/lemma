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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
    (n : Nat) (hn : 0 < n) (i j : Nat)
    (hi : i < 2 * n) (hj : j < 2 * n) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension,
    hi, hj]

theorem centeredRadialPatchVertex_strictInterior
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n) :
    let x := fkIsingSquareCenteredRadialPatchVertex n
      ⟨I, by omega⟩ ⟨J, by omega⟩
    fkIsingSquareDirectionAvailable n x .east ∧
      fkIsingSquareDirectionAvailable n x .north ∧
      fkIsingSquareDirectionAvailable n x .west ∧
      fkIsingSquareDirectionAvailable n x .south := by
  dsimp
  simp [fkIsingSquareDirectionAvailable,
    fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (heven : Even (I + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J, by omega⟩) := by
  let ii : Fin (2 * n) := ⟨I, by omega⟩
  let jj : Fin (2 * n) := ⟨J, by omega⟩
  let x := fkIsingSquareCenteredRadialPatchVertex n ii jj
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    centeredRadialPatchVertex_strictInterior n I J hI0 hI1 hJ0 hJ1
  have hquad := fkIsingSquareBoundaryFullVertexFullObservable_quad
    n hn x heast hnorth hwest hsouth
  change IsingSquareSHolomorphicQuad
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .south hsouth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .west hwest))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .north hnorth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .east heast)) at hquad
  have hoddS : ¬ Even (I - 1 + J) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (I - 1 + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (I + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J, by omega⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ heven]
  simpa only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI : I < 2 * n)
    (hJ0 : 0 < J) (hJ : J < 2 * n)
    (heven : Even (I + J))
    (heast : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .east)
    (hnorth : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .north)
    (hwest : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .west)
    (hsouth : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .south) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J, hJ⟩) := by
  let ii : Fin (2 * n) := ⟨I, hI⟩
  let jj : Fin (2 * n) := ⟨J, hJ⟩
  let x := fkIsingSquareCenteredRadialPatchVertex n ii jj
  have hquad := fkIsingSquareBoundaryFullVertexFullObservable_quad
    n hn x heast hnorth hwest hsouth
  change IsingSquareSHolomorphicQuad
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .south hsouth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .west hwest))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .north hnorth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .east heast)) at hquad
  have hoddS : ¬ Even (I - 1 + J) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (I - 1 + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (I + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J, hJ⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ heven]
  simpa only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
    (n J : Nat) (hn : 0 < n) (hJ0 : 0 < J) (hJ : J < 2 * n)
    (heven : Even ((2 * n - 1) + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
      n (2 * n - 1) J hn (by omega) (by omega) hJ0 hJ heven <;>
    simp [fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf] <;>
    have hmod := Nat.even_iff.mp heven <;> omega


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
    (n I : Nat) (hn : 0 < n) (hI0 : 0 < I) (hI : I < 2 * n)
    (heven : Even (I + (2 * n - 1))) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
      n I (2 * n - 1) hn hI0 hI (by omega) (by omega) heven <;>
    simp [fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf] <;>
    have hmod := Nat.even_iff.mp heven <;> omega

end
end StatMech.Universality

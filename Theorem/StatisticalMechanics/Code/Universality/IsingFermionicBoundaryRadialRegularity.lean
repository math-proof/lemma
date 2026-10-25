/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryRadialPatchFullObservable_quad
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (heven : Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩) := by
  let ii : Fin m := ⟨i, by omega⟩
  let jj : Fin m := ⟨j, by omega⟩
  let x := fkIsingSquareRadialPatchVertex n m hm ii jj
  have heast : fkIsingSquareDirectionAvailable n x .east := by
    simpa [x, ii, jj, fkIsingSquareRadialPatchDirection, heven] using
      fkIsingSquareRadialPatchDirection_available n m hm ii jj
  have hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
  have hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
  have hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, ii, jj, fkIsingSquareDirectionAvailable,
      fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
    have hmod := Nat.even_iff.mp heven
    omega
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
  have hoddS : ¬ Even (i - 1 + j) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (i - 1 + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (i + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ heven]
  simpa only [fkIsingSquareBoundaryRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad


theorem fkIsingSquareBoundaryRadialPatchFullObservable_quad_of_odd
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi0 : 0 < i) (hi1 : i + 1 < m)
    (hj0 : 0 < j) (hj1 : j + 1 < m) (hodd : ¬ Even (i + j)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩)
      (fkIsingSquareBoundaryRadialPatchFullObservable n m hn hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
  let p : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), hodd⟩
  let c := fkIsingSquareRadialPatchDualFullFace n m hm (by omega) p
  have hevenN : Even (i + (j - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hN : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j - 1, by omega⟩ = faceNorthEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenN]
    apply Subtype.ext
    simp only [faceNorthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceNWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hE : fkIsingSquareRadialPatchEdge n m hm
        ⟨i, by omega⟩ ⟨j, by omega⟩ = faceEastEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hodd]
    apply Subtype.ext
    simp only [faceEastEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSEVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hevenS : Even (i - 1 + j) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hS : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j, by omega⟩ = faceSouthEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_east n m hm _ _ hevenS]
    apply Subtype.ext
    simp only [faceSouthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hoddW : ¬ Even (i - 1 + (j - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hW : fkIsingSquareRadialPatchEdge n m hm
        ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ = faceWestEdge n c := by
    rw [fkIsingSquareRadialPatchEdge_eq_north n m hm _ _ hoddW]
    apply Subtype.ext
    simp only [faceWestEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, p, faceSWVertex, fkIsingSquareRadialPatchVertex,
        fkIsingSquareRadialPatchHalf_eq, fkIsingSquareInteriorCellKey,
        fkIsingSquareRadialPatchDualFullFace, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hnotN : (faceNorthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hN]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩
  have hnotE : (faceEastEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hE]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i, by omega⟩ ⟨j, by omega⟩
  have hnotS : (faceSouthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hS]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩
  have hnotW : (faceWestEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    rw [← hW]
    exact fkIsingSquareRadialPatchEdge_not_mem_perimeter
      n m hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  have hquad := fkIsingSquareBoundaryFullFaceFullObservable_quad
    n hn c hnotN hnotE hnotS hnotW
  unfold fkIsingSquareBoundaryRadialPatchFullObservable
  rw [hN, hE, hS, hW]
  exact hquad


end
end StatMech.Universality

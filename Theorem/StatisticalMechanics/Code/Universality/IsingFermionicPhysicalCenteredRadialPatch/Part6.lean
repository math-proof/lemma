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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem centeredRadialPatchDualFullFace_bounds
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) :
    let c := centeredRadialPatchDualFullFace n I J
      hI0 hI1 hJ0 hJ1 hodd
    0 < c.1.1 ∧ c.1.1 + 1 < 2 * n ∧
      0 < c.2.1 ∧ c.2.1 + 1 < 2 * n := by
  dsimp [centeredRadialPatchDualFullFace, centeredRadialHalf]
  have hmod := Nat.not_even_iff.mp hodd
  omega


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) := by
  let c := centeredRadialPatchDualFullFace n I J
    hI0 hI1 hJ0 hJ1 hodd
  have hevenN : Even (I + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩ = faceNorthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenN]
    apply Subtype.ext
    simp only [faceNorthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceNWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J, by omega⟩ = faceEastEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hodd]
    apply Subtype.ext
    simp only [faceEastEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSEVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hevenS : Even (I - 1 + J) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩ = faceSouthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenS]
    apply Subtype.ext
    simp only [faceSouthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hoddW : ¬ Even (I - 1 + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ = faceWestEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddW]
    apply Subtype.ext
    simp only [faceWestEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  obtain ⟨hwest, heast, hsouth, hnorth⟩ :=
    centeredRadialPatchDualFullFace_bounds n I J
      hI0 hI1 hJ0 hJ1 hodd
  have hSWwest : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hSWsouth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWwest : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hNWnorth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    have hc : (c.2.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast hnorth
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    have hc : (c.1.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast heast
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWeast : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hNWsouth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .south := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey]
  have hSEnorth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSEwest : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey]
  have hSWeast : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSWnorth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hnotN : (faceNorthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceNWVertex n c) .east hNWeast
        hNWeast hNWnorth hNWwest hNWsouth
  have hnotE : (faceEastEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSEVertex n c) .north hSEnorth
        hSEeast hSEnorth hSEwest hSEsouth
  have hnotS : (faceSouthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .east hSWeast
        hSWeast hSWnorth hSWwest hSWsouth
  have hnotW : (faceWestEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .north hSWnorth
        hSWeast hSWnorth hSWwest hSWsouth
  have hquad := fkIsingSquareBoundaryFullFaceFullObservable_quad
    n hn c hnotN hnotE hnotS hnotW
  unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservable
  rw [hN, hE, hS, hW]
  exact hquad

end
end StatMech.Universality

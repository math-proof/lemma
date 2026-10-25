/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part8


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem face_difference_of_common_vertex
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn f) -
        FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      fkIsingSquareInteriorRadialIncrement n hn f -
        fkIsingSquareInteriorRadialIncrement n hn e := by
  have he := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn e
  have hf := FKIsingSquareFullIntegratedPrimitive.face_sub_vertex n hn f
  rw [hendpoint] at he
  linarith

theorem face_difference_north (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hnorth : c.2.1 + 1 < 2 * n) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (faceNorthNeighbor n c hnorth) -
        FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceNorthEdge n c, .north)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceNorthEdge n c, .east)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceNorthEastDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceNorthNeighborDart n c hnorth)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceNorthEastDart, faceNorthNeighborDart, faceNorthEdge,
        faceNWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceNorthEastDart, faceNorthEdge, faceNWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceNorthNeighbor n c hnorth := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceNorthNeighborDart, faceNorthNeighbor, faceNorthEdge,
      faceNWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    ring
  rw [heface, hfface] at h
  simpa [e, f, faceNorthEastDart, faceNorthNeighborDart] using h

theorem face_difference_east (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (heast : c.1.1 + 1 < 2 * n) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (faceEastNeighbor n c heast) -
        FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceEastEdge n c, .south)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceEastEdge n c, .west)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceEastWestDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceEastNeighborDart n c heast)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceEastWestDart, faceEastNeighborDart, faceEastEdge,
        faceSEVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceEastWestDart, faceEastEdge, faceSEVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceEastNeighbor n c heast := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceEastNeighborDart, faceEastNeighbor, faceEastEdge,
      faceSEVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    ring
  rw [heface, hfface] at h
  simpa [e, f, faceEastWestDart, faceEastNeighborDart] using h

theorem face_difference_south (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hsouth : 0 < c.2.1) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (faceSouthNeighbor n c hsouth) -
        FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceSouthEdge n c, .south)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceSouthEdge n c, .west)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceSouthWestDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceSouthNeighborDart n c hsouth)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceSouthWestDart, faceSouthNeighborDart, faceSouthEdge,
        faceSWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceSouthWestDart, faceSouthEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceSouthNeighbor n c hsouth := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceSouthNeighborDart, faceSouthNeighbor, faceSouthEdge,
      faceSWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    have hy := c.2.isLt
    omega
  rw [heface, hfface] at h
  simpa [e, f, faceSouthWestDart, faceSouthNeighborDart] using h

theorem face_difference_west (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hwest : 0 < c.1.1) :
    FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
          (faceWestNeighbor n c hwest) -
        FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn c =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceWestEdge n c, .north)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (faceWestEdge n c, .east)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestEastDart n c)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (faceWestNeighborDart n c hwest)
  have hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f := by
    apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [e, f, faceWestEastDart, faceWestNeighborDart, faceWestEdge,
        faceSWVertex, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have h := face_difference_of_common_vertex n hn e f hendpoint
  have heface : fkIsingSquareFullFaceOfRadialIncidence n hn e = c := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [e, faceWestEastDart, faceWestEdge, faceSWVertex,
      fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite]
  have hfface : fkIsingSquareFullFaceOfRadialIncidence n hn f =
      faceWestNeighbor n c hwest := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    simp [f, faceWestNeighborDart, faceWestNeighbor, faceWestEdge,
      faceSWVertex, fkIsingSquareWedgeFaceKey, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
      fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
      fkIsingSquareInteriorCellKey]
    have hx := c.1.isLt
    omega
  rw [heface, hfface] at h
  simpa [e, f, faceWestEastDart, faceWestNeighborDart] using h

namespace FKIsingSquareFullIntegratedPrimitive

theorem face_laplacian_nonneg_of_interior (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      (FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn) c := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cW := faceWestNeighbor n c hwest
  let cS := faceSouthNeighbor n c hsouth
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  let H := FKIsingSquareFullIntegratedPrimitive.facePrimitive n hn
  let F := fkIsingSquareWiredFullMedialObservable n hn
  have hEN : cE ≠ cN := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cN, faceEastNeighbor, faceNorthNeighbor] at h0
  have hEW : cE ≠ cW := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cW, faceEastNeighbor, faceWestNeighbor] at h0
    omega
  have hES : cE ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cE, cS, faceEastNeighbor, faceSouthNeighbor] at h0
  have hNW : cN ≠ cW := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cW, faceNorthNeighbor, faceWestNeighbor] at h1
  have hNS : cN ≠ cS := by
    intro h
    have h1 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.2.1) h
    simp [cN, cS, faceNorthNeighbor, faceSouthNeighbor] at h1
    omega
  have hWS : cW ≠ cS := by
    intro h
    have h0 := congrArg (fun z : FKIsingSquareFullFaceNode n ↦ z.1.1) h
    simp [cW, cS, faceWestNeighbor, faceSouthNeighbor] at h0
    omega
  have hLap : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      (H cE - H c) + (H cN - H c) +
        (H cW - H c) + (H cS - H c) := by
    unfold isingFiniteGraphLaplacian
    simp only [fkIsingSquareFullFace_neighborFinset n c heast hnorth hwest hsouth]
    change ∑ y ∈ {cE, cN, cW, cS}, (H y - H c) = _
    simp [hEN, hEW, hES, hNW, hNS, hWS]
    ring
  have hdN := face_difference_north n hn c hnorth
  have hdE := face_difference_east n hn c heast
  have hdS := face_difference_south n hn c hsouth
  have hdW := face_difference_west n hn c hwest
  change H cN - H c = _ at hdN
  change H cE - H c = _ at hdE
  change H cS - H c = _ at hdS
  change H cW - H c = _ at hdW
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .horizontal := by
    dsimp [eN, faceNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .vertical := by
    dsimp [eE, faceEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .horizontal := by
    dsimp [eS, faceSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .vertical := by
    dsimp [eW, faceWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eN haxisN with
    ⟨_, hNE, _, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eE haxisE with
    ⟨hEW, _, hES, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eS haxisS with
    ⟨hSW, _, hSS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eW haxisW with
    ⟨_, hWE, _, hWN⟩
  have hdiv : isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) H c =
      isingPrimalProjectionDivergence (F eN) (F eE) (F eS) (F eW) := by
    rw [hLap, hdE, hdN, hdW, hdS]
    simp_rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
    unfold isingPrimalProjectionDivergence
    rw [hNE, hNN, hEW, hES, hSW, hSS, hWE, hWN]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _
    (fkIsingSquareFullFaceFullObservable_quad n hn c)

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality

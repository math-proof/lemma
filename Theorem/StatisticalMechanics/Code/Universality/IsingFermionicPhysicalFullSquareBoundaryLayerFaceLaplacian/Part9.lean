/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part8


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem face_difference_of_common_vertex
    (n : Nat) (hn : 0 < n)
    (e f : FKIsingSquareInteriorRadialIncidence n hn)
    (hendpoint : fkIsingSquareInteriorRadialEndpoint n hn e =
      fkIsingSquareInteriorRadialEndpoint n hn f) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn f) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (fkIsingSquareFullFaceOfRadialIncidence n hn e) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn f -
        fkIsingSquareBoundaryLayerRadialIncrement n hn e := by
  have he := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn e
  have hf := fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn f
  rw [hendpoint] at he
  linarith

theorem face_difference_north (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) (hnorth : c.2.1 + 1 < 2 * n) :
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceNorthNeighbor n c hnorth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceNorthEdge n c, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceEastNeighbor n c heast) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceEastEdge n c, .south)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceSouthNeighbor n c hsouth) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceSouthEdge n c, .south)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
          (faceWestNeighbor n c hwest) -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive c =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
          (.dart (faceWestEdge n c, .north)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn
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

namespace FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem face_laplacian_nonneg_of_interior (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1) :
    0 ≤ isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n)
      ((fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive) c := by
  classical
  let cE := faceEastNeighbor n c heast
  let cN := faceNorthNeighbor n c hnorth
  let cW := faceWestNeighbor n c hwest
  let cS := faceSouthNeighbor n c hsouth
  let eN := faceNorthEdge n c
  let eE := faceEastEdge n c
  let eS := faceSouthEdge n c
  let eW := faceWestEdge n c
  let H := (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).facePrimitive
  let F := fkIsingSquareBoundaryFullMedialObservable n hn
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
    simp [fkIsingSquareInteriorCellKey] at hnorth ⊢
    omega
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    simp [fkIsingSquareInteriorCellKey] at heast ⊢
    omega
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have heN : eN.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eN, faceNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceNWVertex n c) .east (faceNW_east_available n c)
        (faceNW_east_available n c) hNWnorth hNWwest
        (faceNW_south_available n c)
  have heE : eE.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eE, faceEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSEVertex n c) .north (faceSE_north_available n c)
        hSEeast (faceSE_north_available n c) (faceSE_west_available n c)
        hSEsouth
  have heS : eS.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eS, faceSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .east (faceSW_east_available n c)
        (faceSW_east_available n c) (faceSW_north_available n c) hSWwest
        hSWsouth
  have heW : eW.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [eW, faceWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .north (faceSW_north_available n c)
        (faceSW_east_available n c) (faceSW_north_available n c) hSWwest
        hSWsouth
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
    simp only [fkIsingSquareBoundaryFullFace_neighborFinset n c heast hnorth hwest hsouth]
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
    rw [fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eE heE .west,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eN heN .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .north,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eW heW .east,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .south,
        fkIsingSquareBoundaryPrimitiveIncrement_eq_normSq_full_projection
          n hn eS heS .west]
    unfold isingPrimalProjectionDivergence
    rw [hNE, hNN, hEW, hES, hSW, hSS, hWE, hWN]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonneg _ _ _ _
    (fkIsingSquareBoundaryFullFaceFullObservable_quad n hn c heN heE heS heW)

end FKIsingSquareBoundaryLayerIntegratedPrimitive
end
end StatMech.Universality

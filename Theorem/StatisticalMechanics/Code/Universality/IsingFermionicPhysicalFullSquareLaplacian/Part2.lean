/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem vertex_difference_north (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .north hnorth) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexNorthEdge n x hnorth, .west)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexNorthEdge n x hnorth, .north)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (northCenterDart n x hnorth hwest)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (northNeighborDart n x hnorth hwest)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .west) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexNorthEdge n x hnorth, .north)
    symm
    simp [fullVertexNorthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, northCenterDart, northNeighborDart,
    fullVertexNorthEdge] using h

theorem vertex_difference_east (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .east heast) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexEastEdge n x heast, .west)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexEastEdge n x heast, .north)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (eastCenterDart n x heast hnorth)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (eastNeighborDart n x heast hnorth)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .west) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexEastEdge n x heast, .north)
    symm
    simp [fullVertexEastEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, eastCenterDart, eastNeighborDart,
    fullVertexEastEdge] using h

theorem vertex_difference_south (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hsouth : fkIsingSquareDirectionAvailable n x .south)
    (heast : fkIsingSquareDirectionAvailable n x .east) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .south hsouth) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexSouthEdge n x hsouth, .east)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexSouthEdge n x hsouth, .south)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (southCenterDart n x hsouth heast)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (southNeighborDart n x hsouth heast)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .east) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexSouthEdge n x hsouth, .south)
    symm
    simp [fullVertexSouthEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  simpa [e, f, southCenterDart, southNeighborDart,
    fullVertexSouthEdge] using h

theorem vertex_difference_west (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
          (fkIsingSquareNeighbor n x .west hwest) -
        FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn x =
      fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexWestEdge n x hwest, .east)) -
        fkIsingSquareWiredPrimitiveIncrement n hn
          (.dart (fullVertexWestEdge n x hwest, .south)) := by
  let e : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (westCenterDart n x hwest hsouth)
  let f : FKIsingSquareInteriorRadialIncidence n hn :=
    Quot.mk _ (westNeighborDart n x hwest hsouth)
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn e =
      fkIsingSquareFullFaceOfRadialIncidence n hn f := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .east) =
      fkIsingSquareWedgeFaceKey n
        (fullVertexWestEdge n x hwest, .south)
    symm
    simp [fullVertexWestEdge, fkIsingSquareWedgeFaceKey,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareSideCorner, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    constructor <;> rfl
  have h := vertex_difference_of_common_face n hn e f hface
  have hcenter : fkIsingSquareDartEndpoint n
      (fullVertexWestEdge n x hwest, .east) = x := by
    unfold fkIsingSquareDartEndpoint fullVertexWestEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hneighbor : fkIsingSquareDartEndpoint n
      (fullVertexWestEdge n x hwest, .south) =
        fkIsingSquareNeighbor n x .west hwest := by
    unfold fkIsingSquareDartEndpoint fullVertexWestEdge
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  change FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .south)) -
      FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
        (fkIsingSquareDartEndpoint n
          (fullVertexWestEdge n x hwest, .east)) = _ at h
  rw [hcenter, hneighbor] at h
  simpa [e, f, westCenterDart, westNeighborDart,
    fullVertexWestEdge] using h

namespace FKIsingSquareFullIntegratedPrimitive

theorem vertex_laplacian_nonpos_of_interior (n : Nat) (hn : 0 < n)
    (x : (fkSquareBoxPlanar n).V)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn) x ≤ 0 := by
  let xE := fkIsingSquareNeighbor n x .east heast
  let xN := fkIsingSquareNeighbor n x .north hnorth
  let xW := fkIsingSquareNeighbor n x .west hwest
  let xS := fkIsingSquareNeighbor n x .south hsouth
  let eN := fullVertexNorthEdge n x hnorth
  let eE := fullVertexEastEdge n x heast
  let eS := fullVertexSouthEdge n x hsouth
  let eW := fullVertexWestEdge n x hwest
  let H := FKIsingSquareFullIntegratedPrimitive.vertexPrimitive n hn
  let F := fkIsingSquareWiredFullMedialObservable n hn
  have hEN : xE ≠ xN := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xN, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hEW : xE ≠ xW := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hES : xE ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xE, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hNW : xN ≠ xW := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [xN, xW, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hNS : xN ≠ xS := by
    intro h
    have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [xN, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h1
  have hWS : xW ≠ xS := by
    intro h
    have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [xW, xS, fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at h0
  have hLap : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      (H xE - H x) + (H xN - H x) +
        (H xW - H x) + (H xS - H x) := by
    unfold isingFiniteGraphLaplacian
    rw [fkIsingSquareFullVertex_neighborFinset n x heast hnorth hwest hsouth]
    simp [xE, xN, xW, xS, hEN, hEW, hES, hNW, hNS, hWS]
    ring
  have hdN := vertex_difference_north n hn x hnorth hwest
  have hdE := vertex_difference_east n hn x heast hnorth
  have hdS := vertex_difference_south n hn x hsouth heast
  have hdW := vertex_difference_west n hn x hwest hsouth
  change H xN - H x = _ at hdN
  change H xE - H x = _ at hdE
  change H xS - H x = _ at hdS
  change H xW - H x = _ at hdW
  have haxisN : (fkIsingSquareOrientedEdge n eN).axis = .vertical := by
    dsimp [eN, fullVertexNorthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisE : (fkIsingSquareOrientedEdge n eE).axis = .horizontal := by
    dsimp [eE, fullVertexEastEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisS : (fkIsingSquareOrientedEdge n eS).axis = .vertical := by
    dsimp [eS, fullVertexSouthEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have haxisW : (fkIsingSquareOrientedEdge n eW).axis = .horizontal := by
    dsimp [eW, fullVertexWestEdge]
    rw [fkIsingSquareOrientedEdge_directionEdge]
    rfl
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eN haxisN with
    ⟨hNW, _, _, hNN⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eE haxisE with
    ⟨hEW, _, _, hEN⟩
  rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn eS haxisS with
    ⟨_, hSE, hSS, _⟩
  rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn eW haxisW with
    ⟨_, hWE, hWS, _⟩
  have hdiv : isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G H x =
      isingPrimalProjectionDivergence (F eN) (F eE) (F eS) (F eW) := by
    rw [hLap, hdE, hdN, hdW, hdS]
    simp_rw [fkIsingSquareWiredPrimitiveIncrement_eq_normSq_full_projection]
    unfold isingPrimalProjectionDivergence
    rw [hNW, hNN, hEW, hEN, hSE, hSS, hWE, hWS]
    ring
  rw [hdiv, ← isingPrimalPrimitiveLaplacian_eq_projectionDivergence]
  exact isingPrimalPrimitiveLaplacian_nonpos_of_rotated_quad _ _ _ _
    (fkIsingSquareFullVertexFullObservable_quad
      n hn x heast hnorth hwest hsouth)

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part17


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem topBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top k0, .west) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem topBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (topBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.top, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let d := topBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (topBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, topBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, topBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .east heast .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, topBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .east = .west := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .west hwest .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .top k1, .north) := rfl

theorem topBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [topBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem topBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    topBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  simp [topBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide,
    fkIsingSquareDartEndpoint, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
    fkIsingSquareMarkedB, fkIsingSquareNeighbor,
    fkIsingSquareNeighborSite, k0] at he
  have hk := k.isLt
  omega

theorem topBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .top k1, .north) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .top k1, .north) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .top k1, .north) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega


theorem topBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (topBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := topBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    simpa [d, k1] using topBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact topBoundaryCrossDart_ne_source n hn k hd
    · exact topBoundaryCrossDart_not_boundary n hn k ⟨.west j, hd.symm⟩
  have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    rw [fkIsingSquareWiredBoundaryReverse, hmate]
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · have hend := congrArg (fkIsingSquareDartEndpoint n) hd
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hend
      simp [fkIsingSquareWiredSourceDart, fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart, fkIsingSquareDartEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareCornerSide, fkIsingSquareEndpointForDirection,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareMarkedA, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k1] at h0
      omega
    · exact topBoundaryCrossMate_not_boundary n hn k ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, topBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring


theorem top_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := topBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .top k1, .north) := by
    simpa [d, k1] using topBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (topBoundaryCrossDart_ne_source n hn k)
      (topBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, topBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .top k1, .north)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .top k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .top k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .north)) := hcross.symm
      _ = _ := by simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
          fkIsingSquareBoundaryLayerInwardSide] using hstandard
  have hinv3 : (isingLambda⁻¹) ^ 3 = -isingLambda := by
    field_simp [isingLambda_ne]
    rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
      isingLambda_sq]
    norm_num [Complex.I_sq]
  calc
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k0, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k0, .west)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .top k1, .east)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring


theorem top_boundary_vertex_difference_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.top, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.top, k1)
    let e := fkIsingSquarePerimeterEdge n .top k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.top, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.top, k1)
  let ep := fkIsingSquarePerimeterEdge n .top k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .east), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .south), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let r0 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d0
  let r1 : FKIsingSquareInteriorRadialIncidence n hn := Quot.mk _ d1
  have hend0 : fkIsingSquareInteriorRadialEndpoint n hn r0 = x0 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r0, d0, ep, x0, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0]
  have hend1 : fkIsingSquareInteriorRadialEndpoint n hn r1 = x1 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [r1, d1, ep, x1, fkIsingSquareInteriorRadialEndpoint,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareSideCorner,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hface : fkIsingSquareFullFaceOfRadialIncidence n hn r0 =
      fkIsingSquareFullFaceOfRadialIncidence n hn r1 := by
    apply fkIsingSquareInteriorCellKey_injective n
    simp only [fkIsingSquareFullFaceOfRadialIncidence_key]
    change fkIsingSquareWedgeFaceKey n (ep, .east) =
      fkIsingSquareWedgeFaceKey n (ep, .south)
    simp [ep, fkIsingSquareWedgeFaceKey,
      fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
      fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, k0] <;> ring_nf
  have h0 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r0
  have h1 :=
    fkIsingSquareBoundaryLayerCoordinateOneForm_face_sub_vertex n hn r1
  rw [hend0, hface] at h0
  rw [hend1] at h1
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .east)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .south)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .top k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .top k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hcomp
  linarith

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

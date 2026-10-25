/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part15


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem rightBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right k0, .east) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem rightBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (rightBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.right, k1)
  let hnorth : fkIsingSquareDirectionAvailable n x .north := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hsouth : fkIsingSquareDirectionAvailable n x .south := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let d := rightBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (rightBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, rightBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .south := by
    simp [d, rightBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .south hsouth .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, rightBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .south = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      x, fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .north hnorth .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .right k1, .south) := rfl

theorem rightBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [rightBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem rightBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    rightBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have he := congrArg
    (fun d => (fkIsingSquareDartEndpoint n d).1 0) h
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  simp [rightBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
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

theorem rightBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .right k1, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .right k1, .south) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .right k1, .south) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega


theorem rightBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (rightBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := rightBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
    simpa [d, k1] using rightBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact rightBoundaryCrossDart_ne_source n hn k hd
    · exact rightBoundaryCrossDart_not_boundary n hn k
        ⟨.west j, hd.symm⟩
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
    · exact rightBoundaryCrossMate_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, rightBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring


theorem right_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := rightBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .right k1, .south) := by
    simpa [d, k1] using rightBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (rightBoundaryCrossDart_ne_source n hn k)
      (rightBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, rightBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .right k1, .south)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .right k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .right k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .south)) :=
        hcross.symm
      _ = _ := by simpa only [D, fkIsingSquareBoundaryLayerEndpointSide,
          fkIsingSquareBoundaryLayerInwardSide] using hstandard
  have hinv3 : (isingLambda⁻¹) ^ 3 = -isingLambda := by
    field_simp [isingLambda_ne]
    rw [show isingLambda ^ 4 = (isingLambda ^ 2) ^ 2 by ring,
      isingLambda_sq]
    norm_num [Complex.I_sq]
  calc
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k0, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k0, .east)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .right k1, .west)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring


theorem right_boundary_vertex_difference_south
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let x0 := fkIsingSquareBoundaryVertex n (.right, k0)
    let x1 := fkIsingSquareBoundaryVertex n (.right, k1)
    let e := fkIsingSquarePerimeterEdge n .right k0
    (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x0 -
        (fkIsingSquareBoundaryLayerCoordinateOneForm n hn).vertexPrimitive x1 =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) -
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x0 := fkIsingSquareBoundaryVertex n (.right, k0)
  let x1 := fkIsingSquareBoundaryVertex n (.right, k1)
  let ep := fkIsingSquarePerimeterEdge n .right k0
  let d0 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .west), by
    simp [ep, fkIsingSquareWedgeFaceKey, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareInteriorFaceKey, k0]
    omega⟩
  let d1 : FKIsingSquareInteriorRadialDart n := ⟨(ep, .north), by
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
    simp [r0, r1, d0, d1, ep, fkIsingSquareWedgeFaceKey,
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
      (.dart (ep, .west)) at h0
  change _ = fkIsingSquareBoundaryPrimitiveIncrement n hn
      (.dart (ep, .north)) at h1
  have hstd := fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    n hn .right k0
  have hcomp :=
    fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
      n hn .right k0
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .west)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .south)) at hstd
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (ep, .north)) at hcomp
  linarith

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

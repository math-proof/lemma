/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part10


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem bottomBoundaryCrossDart_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .bottom k0, .east) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k0] at hwire
  simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite] at hwire
  omega

theorem bottomBoundaryCrossDart_bondMate
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    fkIsingSquareWiredBondMate n hn (bottomBoundaryCrossDart n k) =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let x := fkIsingSquareBoundaryVertex n (.bottom, k1)
  let heast : fkIsingSquareDirectionAvailable n x .east := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
    omega
  let hwest : fkIsingSquareDirectionAvailable n x .west := by
    simp [x, fkIsingSquareDirectionAvailable,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1]
  let d := bottomBoundaryCrossDart n k
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d (bottomBoundaryCrossDart_not_boundary n hn k)]
  have hprevEdge : fkIsingSquareDartEndpoint n d = x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [d, bottomBoundaryCrossDart, x, fkIsingSquarePerimeterEdge,
        fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
        fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareNeighbor, fkIsingSquareNeighborSite, k0, k1] <;> ring
  have hdirection : fkIsingSquareDartDirection n d = .west := by
    simp [d, bottomBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner]
  have hdrepr : d =
      fkIsingSquareDirectionDart n x .west hwest .counterclockwise := by
    apply fkIsingSquareDart_key_injective n
    simp only [fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction]
    rw [hprevEdge, hdirection]
    simp [d, bottomBoundaryCrossDart, fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide]
  rw [hdrepr]
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hdir : fkIsingSquareNextDirection n x .west = .east := by
    simp [fkIsingSquareNextDirection,
      fkIsingSquareDirectionAvailable, x,
      fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite]
    omega
  calc
    _ = fkIsingSquareDirectionDart n x .east heast .clockwise :=
      fkIsingSquareDirectionDart_congr n x hdir _ _ _
    _ = (fkIsingSquarePerimeterEdge n .bottom k1, .south) := rfl

theorem bottomBoundaryCrossDart_ne_source
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ≠ fkIsingSquareWiredSourceDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomBoundaryCrossDart, fkIsingSquareWiredSourceDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem bottomBoundaryCrossDart_ne_terminal
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    bottomBoundaryCrossDart n k ≠ fkIsingSquareWiredTerminalDart n hn := by
  intro h
  have hs := congrArg Prod.snd h
  simp [bottomBoundaryCrossDart, fkIsingSquareWiredTerminalDart,
    fkIsingSquareWiredBoundaryDart, fkIsingSquareDirectionDart,
    fkIsingSquareEndpointForDirection, fkIsingSquareCornerSide] at hs

theorem bottomBoundaryCrossMate_not_boundary
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    (fkIsingSquarePerimeterEdge n .bottom k1, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  change (fkIsingSquarePerimeterEdge n .bottom k1, .south) ∉
    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
  rintro ⟨i, hi⟩
  have hwire := fkIsingSquareWiredBoundaryDart_endpoint_mem_wiredArc n hn i
  have hend := congrArg (fkIsingSquareDartEndpoint n) hi
  change fkIsingSquareDartEndpoint n
      (fkIsingSquareWiredBoundaryDart n hn i) =
    fkIsingSquareDartEndpoint n
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) at hend
  rw [hend] at hwire
  simp [fkIsingSquareWiredArc, fkIsingSquarePerimeterEdge,
    fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
    fkIsingSquareOrientedEdge_directionEdge,
    fkIsingSquareDirectionEdgeOrientation, fkIsingSquareSideCorner,
    fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite, k1] at hwire
  omega


theorem bottomBoundaryCrossDart_bondPhase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    fkIsingSquareWiredBondPhase n hn (bottomBoundaryCrossDart n k) =
      isingLambda := by
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let d := bottomBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    simpa [d, k1] using bottomBoundaryCrossDart_bondMate n hn k
  have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d
      (fkIsingSquareWiredBondMate n hn d) := by
    intro h
    rcases h with ⟨hd, -⟩ | ⟨j, hd, -⟩
    · exact bottomBoundaryCrossDart_ne_source n hn k hd
    · exact bottomBoundaryCrossDart_not_boundary n hn k
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
    · exact bottomBoundaryCrossMate_not_boundary n hn k
        ⟨.west j, hd.symm⟩
  have hturn : fkIsingSquareWiredBondTurn n hn d
      (fkIsingSquareWiredBondMate n hn d) = 2 := by
    rw [fkIsingSquareWiredBondTurn, if_neg hfwd, if_neg hrev, hmate]
    simp [fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareSignedEighthTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, FKIsingSquareDirection.eighthTurn,
      d, bottomBoundaryCrossDart, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]
  unfold fkIsingSquareWiredBondPhase
  rw [hturn, isingLambda]
  congr 1
  push_cast
  ring


theorem bottom_boundary_inward_observable_phase
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
    D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) =
      -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let d := bottomBoundaryCrossDart n k
  have hmate : fkIsingSquareWiredBondMate n hn d =
      (fkIsingSquarePerimeterEdge n .bottom k1, .south) := by
    simpa [d, k1] using bottomBoundaryCrossDart_bondMate n hn k
  have hbond := fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
    n hn d (bottomBoundaryCrossDart_ne_source n hn k)
      (bottomBoundaryCrossDart_ne_terminal n hn k)
  have hcross : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
        isingLambda := by
    change D.fermionicObservable
        (.bond (fkIsingSquareWiredBondMate n hn d)) =
      D.fermionicObservable (.bond d) *
        fkIsingSquareWiredBondPhase n hn d at hbond
    rw [hmate, bottomBoundaryCrossDart_bondPhase n hn k] at hbond
    calc
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) =
        D.fermionicObservable
          (.bond (fkIsingSquarePerimeterEdge n .bottom k1, .south)) := by
            rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = D.fermionicObservable (.bond d) * isingLambda := hbond
      _ = D.fermionicObservable (.dart d) * isingLambda := by
        rw [fkIsingSquareBoundaryLayer_fermionicObservable_incidence]
      _ = _ := by rfl
  have hstandard := fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    n hn .bottom k1
  have hcomplement :=
    fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
      n hn .bottom k0
  have hlink : D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
          isingLambda =
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
          isingLambda⁻¹ := by
    calc
      _ = D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .south)) :=
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
        (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .north)) =
      D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
        isingLambda⁻¹ := by
      simpa only [D, fkIsingSquareBoundaryLayerComplementEndpointSide,
        fkIsingSquareBoundaryLayerComplementInwardSide] using hcomplement
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k0, .east)) *
            isingLambda) * (isingLambda⁻¹) ^ 2 := by
      field_simp [isingLambda_ne]
    _ = (D.fermionicObservable
          (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
            isingLambda⁻¹) * (isingLambda⁻¹) ^ 2 := by rw [hlink]
    _ = -isingLambda * D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) := by
      calc
        _ = D.fermionicObservable
              (.dart (fkIsingSquarePerimeterEdge n .bottom k1, .west)) *
            (isingLambda⁻¹) ^ 3 := by ring
        _ = _ := by rw [hinv3]; ring

theorem isingSquareSHolomorphicQuad_bottom_projection_cycle
    (south west north east : Complex)
    (h : IsingSquareSHolomorphicQuad south west north east) :
    isingProj 1 north = isingProj 1 east ∧
      isingProj (-Complex.I) west = isingProj (-Complex.I) north := by
  rcases h with ⟨hSW, hNE, hdiag⟩
  constructor <;>
    apply Complex.ext <;>
    simp [isingProj, Complex.ext_iff] at hSW hNE hdiag ⊢ <;>
    linarith


theorem isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition
    (north east west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj 1 north) =
      -2 * Complex.normSq (isingProj 1 north) -
        Complex.normSq (isingProj (-Complex.I) east) -
        Complex.normSq (isingProj 1 west) := by
  rw [isingLambda_val] at hphase
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hden : 1 + Real.sqrt 2 ≠ 0 := by positivity
  simp [isingPrimalProjectionDivergenceWithoutSouth, isingProj,
    Complex.ext_iff, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, isingFermionicGhostCoefficient,
    hsqrt_ne] at hNE hWN hphase ⊢
  field_simp [hsqrt_ne, hden] at hphase ⊢
  have hEre : east.re = north.re := by linarith
  have hNim : north.im = -(1 + Real.sqrt 2) * north.re := by
    linarith [hphase.1]
  have hWim : west.im = north.re + north.im - west.re := by
    linarith [hWN.1]
  rw [hEre, hWim, hNim]
  ring_nf
  nlinarith

theorem isingPrimalProjectionDivergenceWithoutSouth_bottom_add_ghost_nonpos
    (north east west : Complex)
    (hNE : isingProj 1 north = isingProj 1 east)
    (hWN : isingProj (-Complex.I) west = isingProj (-Complex.I) north)
    (hphase : isingProj (-Complex.I) north =
      -isingLambda * isingProj 1 north) :
    isingPrimalProjectionDivergenceWithoutSouth north east west +
        isingFermionicGhostCoefficient *
          Complex.normSq (isingProj 1 north) ≤ 0 := by
  rw [isingPrimalProjectionDivergenceWithoutSouth_bottom_decomposition
    north east west hNE hWN hphase]
  have hN := Complex.normSq_nonneg (isingProj 1 north)
  have hE := Complex.normSq_nonneg (isingProj (-Complex.I) east)
  have hW := Complex.normSq_nonneg (isingProj 1 west)
  linarith


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality

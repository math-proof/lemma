/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryPrimitiveIncrement_bondDartMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquareWiredBondMate n hn d)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart d) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [<- fkIsingSquareBoundaryLayer_fermionicObservable_incidence
      n hn (fkIsingSquareWiredBondMate n hn d),
    fkIsingSquareBoundaryLayer_fermionicObservable_bondMate
      n hn d hsource hterminal,
    Complex.normSq_mul, fkIsingSquareWiredBondPhase_normSq, mul_one,
    fkIsingSquareBoundaryLayer_fermionicObservable_incidence]

theorem fkIsingSquareBoundaryPrimitiveIncrement_inward_eq_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_endpoint,
    Complex.normSq_mul]
  have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
    rw [isingLambda_inv_val]
    norm_num [Complex.normSq_apply]
  rw [hlam, mul_one]

theorem fkIsingSquareBoundaryPrimitiveIncrement_complement_inward_eq_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) := by
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint,
    Complex.normSq_mul]
  have hlam : Complex.normSq isingLambda⁻¹ = 1 := by
    rw [isingLambda_inv_val]
    norm_num [Complex.normSq_apply]
  rw [hlam, mul_one]

theorem fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) :
    fkIsingSquareWiredDirectedTangent n hn z *
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          z ^ 2 =
      (fkIsingSquareBoundaryPrimitiveIncrement n hn z : Complex) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let phase := fkIsingSquareWiredDirectedPhase n hn z
  have hphase : forall omega, z ∈ D.exploration omega ->
      D.windingPhase omega z ^ 2 = phase ^ 2 := by
    intro omega hz
    exact fkIsingSquareBoundaryLayer_windingPhase_sq n hn omega z hz
  have hobs := D.fermionicObservable_eq_signedExplorationMass_mul_phase
    z phase hphase
  have hnorm : Complex.normSq phase = 1 := by
    simpa only [phase] using fkIsingSquareWiredDirectedPhase_normSq n hn z
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  rw [hobs]
  let mass := D.signedExplorationMass z phase
  change fkIsingSquareWiredDirectedTangent n hn z *
      ((mass : Complex) * phase) ^ 2 =
    (Complex.normSq ((mass : Complex) * phase) : Complex)
  calc
    fkIsingSquareWiredDirectedTangent n hn z *
        ((mass : Complex) * phase) ^ 2 =
      (mass : Complex) ^ 2 *
        (fkIsingSquareWiredDirectedTangent n hn z * phase ^ 2) := by ring
    _ = (mass : Complex) ^ 2 := by
      rw [fkIsingSquareWiredDirectedTangent_mul_phase_sq]
      ring
    _ = (Complex.normSq ((mass : Complex) * phase) : Complex) := by
      rw [Complex.normSq_mul, hnorm, mul_one]
      simp [Complex.normSq_apply]
      ring


theorem fkIsingSquareBoundaryPrimitiveIncrement_local_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .west)) +
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .east)) =
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .south)) +
        fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_contour_relation n hn e he
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  unfold fkIsingSquareBoundaryPrimitiveIncrement isingPrimitiveIncrement
  change Complex.normSq W + Complex.normSq E =
    Complex.normSq S + Complex.normSq N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_normSq_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_normSq_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour


theorem fkIsingSquareInteriorRadialCell_not_mem_perimeter
    (n : Nat) (e : FKIsingSquareInteriorRadialCell n) :
    e.1.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n := by
  intro he
  simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image] at he
  obtain ⟨side, k, hk⟩ := he
  have hval : e.1.1 = (fkIsingSquarePerimeterEdge n side k).1 := hk.symm
  cases side with
  | bottom =>
      have h := e.2 .east
      have heq : e.1 = fkIsingSquarePerimeterEdge n .bottom k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

  | right =>
      have h := e.2 .east
      have heq : e.1 = fkIsingSquarePerimeterEdge n .right k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

  | top =>
      have h := e.2 .west
      have heq : e.1 = fkIsingSquarePerimeterEdge n .top k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h
  | left =>
      have h := e.2 .west
      have heq : e.1 = fkIsingSquarePerimeterEdge n .left k :=
        Subtype.ext hval
      rw [heq] at h
      simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at h

theorem fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n x d)
    (heast : fkIsingSquareDirectionAvailable n x .east)
    (hnorth : fkIsingSquareDirectionAvailable n x .north)
    (hwest : fkIsingSquareDirectionAvailable n x .west)
    (hsouth : fkIsingSquareDirectionAvailable n x .south) :
    (fkIsingSquareDirectionEdge n x d hd).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
  intro hper
  simp only [fkIsingSquarePerimeterPrimalEdgeFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_image] at hper
  obtain ⟨side, k, hk⟩ := hper
  have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
  have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
  simp [fkIsingSquareDirectionAvailable] at heast hnorth hwest hsouth
  simp only [fkIsingSquarePerimeterEdge, fkIsingSquareDirectionEdge] at hk
  rw [Sym2.eq_iff] at hk
  rcases hk with ⟨hbx, _⟩ | ⟨_, hnbx⟩
  · cases side <;>
      simp [fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite] at hbx <;>
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hbx <;>
      have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) hbx <;>
      simp at h0 h1 <;> omega
  · cases side <;>
      simp [fkIsingSquarePerimeterDirection, fkIsingSquareBoundaryVertex,
        fkIsingSquareBoundarySite, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] at hnbx <;>
      have h0 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 0) hnbx <;>
      have h1 := congrArg (fun z : (fkSquareBoxPlanar n).V => z.1 1) hnbx <;>
      simp at h0 h1 <;> omega


theorem fkIsingSquareBoundaryLayerRadialCell_increment_closed
    (n : Nat) (hn : 0 < n)
    (e : FKIsingSquareInteriorRadialCell n) :
    fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .west) +
        fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .east) =
      fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .south) +
        fkIsingSquareBoundaryLayerRadialIncrement n hn
          (fkIsingSquareInteriorRadialCellIncidence n hn e .north) := by
  change fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .west)) +
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .east)) =
    fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .south)) +
      fkIsingSquareBoundaryPrimitiveIncrement n hn (.dart (e.1, .north))
  exact fkIsingSquareBoundaryPrimitiveIncrement_local_closed n hn e.1
    (fkIsingSquareInteriorRadialCell_not_mem_perimeter n e)

theorem fkIsingSquareBoundary_fermionicObservable_opposite_sum
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (he : e.1 ∉ fkIsingSquarePerimeterPrimalEdgeFinset n) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .west)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .east)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .south)) +
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (e, .north)) := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let W := D.fermionicObservable (.dart (e, .west))
  let E := D.fermionicObservable (.dart (e, .east))
  let S := D.fermionicObservable (.dart (e, .south))
  let N := D.fermionicObservable (.dart (e, .north))
  have hcontour : W - E = Complex.I * (S - N) := by
    simpa only [W, E, S, N, D] using
      fkIsingSquareBoundary_fermionicObservable_contour_relation n hn e he
  have hline (z : FKIsingSquareWiredCarrier n) :
      (starRingEnd Complex) (D.fermionicObservable z) =
        fkIsingSquareWiredDirectedTangent n hn z * D.fermionicObservable z := by
    apply conj_eq_tangent_mul_of_tangent_mul_sq_eq_normSq
    simpa only [D, fkIsingSquareBoundaryPrimitiveIncrement,
      isingPrimitiveIncrement] using
        fkIsingSquareBoundary_tangent_mul_observable_sq_eq_increment n hn z
  change W + E = S + N
  cases haxis : (fkIsingSquareOrientedEdge n e).axis with
  | horizontal =>
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_horizontal_sum_balance W E S N
      · simpa only [W, hW, one_mul] using hline (.dart (e, .west))
      · simpa only [E, hE, neg_mul, one_mul] using hline (.dart (e, .east))
      · simpa only [S, hS] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul] using hline (.dart (e, .north))
      · exact hcontour
  | vertical =>
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨hW, hE, hS, hN⟩
      apply isingFermionic_vertical_sum_balance W E S N
      · simpa only [W, hW, neg_mul] using hline (.dart (e, .west))
      · simpa only [E, hE] using hline (.dart (e, .east))
      · simpa only [S, hS, one_mul] using hline (.dart (e, .south))
      · simpa only [N, hN, neg_mul, one_mul] using hline (.dart (e, .north))
      · exact hcontour

end
end StatMech.Universality

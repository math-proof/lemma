/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part3


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega <->
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerEndpointSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  let a : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerEndpointSide side)
  change a ∈ fkIsingSquareWiredExplorationOrder n hn omega' <->
    b ∈ fkIsingSquareWiredExplorationOrder n hn omega'
  have hm : FKIsingMedialDart.localMate omega'
      (e, fkIsingSquareBoundaryLayerInwardSide side) =
        (e, fkIsingSquareBoundaryLayerEndpointSide side) := by
    exact fkIsingSquareBoundaryLayer_localMate n omega side k
  constructor
  · intro ha
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerInwardSide side) ha
    exact hpair.elim (fun h => h.mem (by simp [b, hm]))
      (fun h => h.mem (by simp [b, hm]))
  · intro hb
    have hinv := FKIsingMedialDart.localMate_involutive omega'
      (e, fkIsingSquareBoundaryLayerInwardSide side)
    have hm' : FKIsingMedialDart.localMate omega'
        (e, fkIsingSquareBoundaryLayerEndpointSide side) =
          (e, fkIsingSquareBoundaryLayerInwardSide side) := by
      rw [<- hm]
      exact hinv
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerEndpointSide side) hb
    exact hpair.elim (fun h => h.mem (by simp [a, hm']))
      (fun h => h.mem (by simp [a, hm']))


theorem fkIsingSquareBoundaryLayer_winding_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) - Real.pi / 2 := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  have hclosed : setClosed e.1 omega' = omega' := by
    exact setClosed_fkIsingSquareClosePerimeter_perimeterEdge
      n omega side k
  change fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerEndpointSide side)) =
    fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerInwardSide side)) - Real.pi / 2
  change fkIsingSquareWiredPathUsesLocalSide n hn omega' e
      (fkIsingSquareBoundaryLayerInwardSide side) at hmem
  cases side with
  | bottom =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | right =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | top =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h
  | left =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerInwardSide,
        fkIsingSquareBoundaryLayerEndpointSide] using h


theorem fkIsingSquareBoundaryLayer_windingPhase_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerEndpointSide side)
  have hw := fkIsingSquareBoundaryLayer_winding_endpoint
    n hn omega side k hmem
  change Complex.exp (Complex.I * (((D.winding omega b) / 2 : Real) :
      Complex)) =
    Complex.exp (Complex.I * (((D.winding omega a) / 2 : Real) :
      Complex)) * isingLambda⁻¹
  rw [hw]
  rw [show isingLambda⁻¹ =
      Complex.exp (-((Real.pi / 4 : Real) : Complex) * Complex.I) by
    rw [isingLambda, <- Complex.exp_neg]
    congr 1
    ring]
  rw [<- Complex.exp_add]
  congr 1
  push_cast
  ring


theorem fkIsingSquareBoundaryLayer_fermionicSummand_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerEndpointSide side)
  change D.fermionicSummand omega b = D.fermionicSummand omega a * _
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases ha : a ∈ D.exploration omega
  · have hb : b ∈ D.exploration omega :=
      (fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
        n hn omega side k).1 ha
    rw [if_pos ha, if_pos hb,
      fkIsingSquareBoundaryLayer_windingPhase_endpoint n hn omega side k ha]
    ring
  · have hb : b ∉ D.exploration omega := fun h =>
      ha ((fkIsingSquareBoundaryLayer_mem_inward_iff_endpoint
        n hn omega side k).2 h)
    rw [if_neg ha, if_neg hb, zero_mul]


theorem fkIsingSquareBoundaryLayer_fermionicObservable_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side)) * isingLambda⁻¹ := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_endpoint
    n hn omega side k


theorem fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega <->
    (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementEndpointSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  let a : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (e, fkIsingSquareBoundaryLayerComplementEndpointSide side)
  change a ∈ fkIsingSquareWiredExplorationOrder n hn omega' <->
    b ∈ fkIsingSquareWiredExplorationOrder n hn omega'
  have hm : FKIsingMedialDart.localMate omega'
      (e, fkIsingSquareBoundaryLayerComplementInwardSide side) =
        (e, fkIsingSquareBoundaryLayerComplementEndpointSide side) := by
    exact fkIsingSquareBoundaryLayer_complement_localMate n omega side k
  constructor
  · intro ha
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerComplementInwardSide side) ha
    exact hpair.elim (fun h => h.mem (by simp [b, hm]))
      (fun h => h.mem (by simp [b, hm]))
  · intro hb
    have hinv := FKIsingMedialDart.localMate_involutive omega'
      (e, fkIsingSquareBoundaryLayerComplementInwardSide side)
    have hm' : FKIsingMedialDart.localMate omega'
        (e, fkIsingSquareBoundaryLayerComplementEndpointSide side) =
          (e, fkIsingSquareBoundaryLayerComplementInwardSide side) := by
      rw [<- hm]
      exact hinv
    have hpair := fkIsingSquareWired_localMate_infix_explorationOrder
      n hn omega' e (fkIsingSquareBoundaryLayerComplementEndpointSide side) hb
    exact hpair.elim (fun h => h.mem (by simp [a, hm']))
      (fun h => h.mem (by simp [a, hm']))


theorem fkIsingSquareBoundaryLayer_winding_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).winding omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) - Real.pi / 2 := by
  let omega' := fkIsingSquareClosePerimeter n omega
  let e := fkIsingSquarePerimeterEdge n side k
  have hclosed : setClosed e.1 omega' = omega' :=
    setClosed_fkIsingSquareClosePerimeter_perimeterEdge n omega side k
  change fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
    fkIsingSquareWiredLiftedWinding n hn omega'
      (.dart (e, fkIsingSquareBoundaryLayerComplementInwardSide side)) -
        Real.pi / 2
  change fkIsingSquareWiredPathUsesLocalSide n hn omega' e
      (fkIsingSquareBoundaryLayerComplementInwardSide side) at hmem
  cases side with
  | bottom =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | right =>
      have h := fkIsingSquareWired_closed_east_north_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | top =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h
  | left =>
      have h := fkIsingSquareWired_closed_west_south_winding
        n hn omega' e (by simpa [hclosed] using hmem)
      simpa [hclosed, fkIsingSquareBoundaryLayerComplementInwardSide,
        fkIsingSquareBoundaryLayerComplementEndpointSide] using h

theorem fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n))
    (hmem : (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementInwardSide side) :
      FKIsingSquareWiredCarrier n) ∈
        (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).exploration
          omega) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).windingPhase omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementEndpointSide side)
  have hw := fkIsingSquareBoundaryLayer_winding_complement_endpoint
    n hn omega side k hmem
  change Complex.exp (Complex.I * (((D.winding omega b) / 2 : Real) :
      Complex)) =
    Complex.exp (Complex.I * (((D.winding omega a) / 2 : Real) :
      Complex)) * isingLambda⁻¹
  rw [hw]
  rw [show isingLambda⁻¹ =
      Complex.exp (-((Real.pi / 4 : Real) : Complex) * Complex.I) by
    rw [isingLambda, <- Complex.exp_neg]
    congr 1
    ring]
  rw [<- Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicSummand
        omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let a : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementInwardSide side)
  let b : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquareBoundaryLayerComplementEndpointSide side)
  change D.fermionicSummand omega b = D.fermionicSummand omega a * _
  unfold FKIsingDobrushinDomain.fermionicSummand
  by_cases ha : a ∈ D.exploration omega
  · have hb : b ∈ D.exploration omega :=
      (fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
        n hn omega side k).1 ha
    rw [if_pos ha, if_pos hb,
      fkIsingSquareBoundaryLayer_windingPhase_complement_endpoint
        n hn omega side k ha]
    ring
  · have hb : b ∉ D.exploration omega := fun h =>
      ha ((fkIsingSquareBoundaryLayer_mem_complement_inward_iff_endpoint
        n hn omega side k).2 h)
    rw [if_neg ha, if_neg hb, zero_mul]

theorem fkIsingSquareBoundaryLayer_fermionicObservable_complement_endpoint
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) *
            isingLambda⁻¹ := by
  unfold FKIsingDobrushinDomain.fermionicObservable
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro omega _
  exact fkIsingSquareBoundaryLayer_fermionicSummand_complement_endpoint
    n hn omega side k


end
end StatMech.Universality

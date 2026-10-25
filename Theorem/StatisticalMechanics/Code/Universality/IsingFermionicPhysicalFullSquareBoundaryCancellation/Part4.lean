/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem FKIsingSquarePerimeterCancellationSwitchingAt.cancellationAt
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterCancellationSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationAt n hn side k := by
  refine ⟨S.uncut, ?_⟩
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n side k,
      fkIsingSquarePerimeterCancelledSide side)
  let total := ∑ omega, D.fermionicSummand omega z
  have hreindex : (∑ omega, D.fermionicSummand omega z) =
      ∑ omega, D.fermionicSummand (S.pairing omega) z := by
    exact (S.pairing.sum_comp (fun omega ↦ D.fermionicSummand omega z)).symm
  have hneg : total = -total := by
    calc
      total = ∑ omega, D.fermionicSummand (S.pairing omega) z := hreindex
      _ = ∑ omega, -D.fermionicSummand omega z := by
        apply Finset.sum_congr rfl
        intro omega _
        exact S.paired_summand omega
      _ = -total := by simp [total]
  have htwo : (2 : Complex) * total = 0 := by
    linear_combination hneg
  have htotal : total = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [D, z, total, FKIsingDobrushinDomain.fermionicObservable] using htotal

theorem FKIsingSquarePerimeterGlobalPathSwitchingAt.cancellationAt
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterGlobalPathSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationAt n hn side k :=
  S.toCancellationSwitching.cancellationAt


theorem isingF_west_ne_zero_of_ne_zero (X : Complex) (hX : X ≠ 0) :
    isingF 0 X ≠ 0 := by
  intro h
  simp only [isingF] at h
  have hs : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)))
  field_simp [hs] at h
  have hzero : (Real.sqrt 2 : Complex) * 0 = 0 := by ring
  rw [hzero] at h
  have hcoef : (Real.sqrt 2 : Complex) + 1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp at hr
    have hp := Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)
    linarith
  exact hX ((mul_eq_zero.mp h).resolve_right hcoef)


theorem isingF_east_ne_zero_of_ne_zero (X : Complex) (hX : X ≠ 0) :
    isingF 1 X ≠ 0 := by
  intro h
  simp only [isingF] at h
  have hs : (Real.sqrt 2 : Complex) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)))
  field_simp [hs] at h
  rw [isingLambda_sq] at h
  have hzero : X = 0 := by simpa using h
  exact hX hzero


theorem fkIsingSquarePerimeter_configIdentity_not_signReversing
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n))
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (hne : (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
      (.dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)) ≠ 0) :
    ¬ ∀ rho,
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
          ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho)
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho
          (.dart (fkIsingSquarePerimeterEdge n side k,
            fkIsingSquarePerimeterCancelledSide side)) := by
  intro h
  have hself := h omega
  simp only [Equiv.refl_apply] at hself
  apply hne
  have htwo : (2 : Complex) *
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand omega
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterCancelledSide side)) = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)


theorem fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc
    (n : Nat) (k : Fin (2 * n)) :
    fkIsingSquareWiredArc n
      (fkIsingSquareDartEndpoint n
        (fkIsingSquarePerimeterEdge n .left k,
          fkIsingSquarePerimeterCancelledSide .left)) := by
  have hm := fkIsingSquareDartEndpoint_mem n
    (fkIsingSquarePerimeterEdge n .left k,
      fkIsingSquarePerimeterCancelledSide .left)
  simp only [fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
    fkIsingSquareDirectionEdge] at hm ⊢
  rw [Sym2.mem_iff] at hm
  rcases hm with hm | hm
  · rw [hm]
    rfl
  · rw [hm]
    simp [fkIsingSquareWiredArc, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareBoundaryVertex,
      fkIsingSquareBoundarySite]


theorem fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (.dart (fkIsingSquarePerimeterEdge n .left k,
        fkIsingSquarePerimeterCancelledSide .left) :
      FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationOrder n hn (FK.edgeSetConfig ∅) := by
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable]
  rw [← fkIsingSquareWiredCompletedLoopGraph_reachable_iff]
  apply fkIsingSquareWiredCompleted_closed_reachable_of_wired_labels
  · simp [fkIsingSquareWiredCarrierPrimalLabel,
      fkIsingSquareWiredArc, fkIsingSquareMarkedA]
  · exact fkIsingSquarePerimeterCancelled_left_endpoint_mem_wiredArc n k


theorem fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
        (FK.edgeSetConfig ∅)
        (.dart (fkIsingSquarePerimeterEdge n .left k,
          fkIsingSquarePerimeterCancelledSide .left)) ≠ 0 := by
  let D := fkIsingSquareWiredDobrushinDomain n hn
  let z : FKIsingSquareWiredCarrier n :=
    .dart (fkIsingSquarePerimeterEdge n .left k,
      fkIsingSquarePerimeterCancelledSide .left)
  have hzOrder : z ∈
      fkIsingSquareWiredExplorationOrder n hn (FK.edgeSetConfig ∅) := by
    simpa only [z] using
      fkIsingSquareWiredPerimeter_cancelled_left_mem_empty_exploration
        n hn k
  have hz : z ∈ D.exploration (FK.edgeSetConfig ∅) := by
    rw [mem_fkIsingSquareWiredDobrushinDomain_exploration_iff_order]
    exact hzOrder
  have hmassR : 0 < D.criticalMass (FK.edgeSetConfig ∅) := by
    unfold FKIsingDobrushinDomain.criticalMass bcProb
    exact div_pos
      (bcWeight_pos (fkSquareBoxPlanar n).G D.wiring
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.1
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.2
        (by norm_num) _)
      (bcZ_pos (fkSquareBoxPlanar n).G D.wiring
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.1
        FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo.2
        (by norm_num))
  have hmass : (D.criticalMass (FK.edgeSetConfig ∅) : Complex) ≠ 0 := by
    exact_mod_cast ne_of_gt hmassR
  unfold FKIsingDobrushinDomain.fermionicSummand
  rw [if_pos hz]
  exact mul_ne_zero hmass (Complex.exp_ne_zero _)


theorem fkIsingSquarePerimeter_configIdentity_not_signReversing_empty_left
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    ¬ ∀ rho,
      (fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand
          ((Equiv.refl _ : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V) ≃ _) rho)
          (.dart (fkIsingSquarePerimeterEdge n .left k,
            fkIsingSquarePerimeterCancelledSide .left)) =
        -(fkIsingSquareWiredDobrushinDomain n hn).fermionicSummand rho
          (.dart (fkIsingSquarePerimeterEdge n .left k,
            fkIsingSquarePerimeterCancelledSide .left)) := by
  exact fkIsingSquarePerimeter_configIdentity_not_signReversing
    n hn .left k (FK.edgeSetConfig ∅)
      (fkIsingSquareWiredPerimeter_cancelled_left_empty_summand_ne_zero
        n hn k)

theorem fkIsingSquarePerimeterEdge_axis (n : Nat)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    (fkIsingSquareOrientedEdge n
      (fkIsingSquarePerimeterEdge n side k)).axis =
      match side with
      | .bottom | .top => .horizontal
      | .right | .left => .vertical := by
  cases side <;>
    simp only [fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection] <;>
    rw [fkIsingSquareOrientedEdge_directionEdge] <;> rfl

theorem fkIsingSquarePerimeterRetained_tangent (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquarePerimeterRetainedSide side)) =
      fkIsingSquareBoundaryTangent side := by
  let e := fkIsingSquarePerimeterEdge n side k
  cases side with
  | bottom =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .bottom k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨h, -, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | right =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .right k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨-, h, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | top =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal :=
        fkIsingSquarePerimeterEdge_axis n .top k
      rcases fkIsingSquareWiredDirectedTangent_horizontal_local n hn e haxis with
        ⟨-, h, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h
  | left =>
      have haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical :=
        fkIsingSquarePerimeterEdge_axis n .left k
      rcases fkIsingSquareWiredDirectedTangent_vertical_local n hn e haxis with
        ⟨h, -, -, -⟩
      simpa [e, fkIsingSquarePerimeterRetainedSide,
        fkIsingSquareBoundaryTangent] using h


end
end StatMech.Universality

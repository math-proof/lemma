/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 →
        ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceReachSet gamma gamma' rho)) := by
  classical
  let lower := (gamma.1.1 : Site 2) 1
  let upper := (gamma'.1.2.1 : Site 2) 1
  let S := rlc_connectorCentralFaceReachSet gamma gamma' rho
  have hlowerLt : lower < upper := by
    have hright := hposition.right_axis_strict
    have hleft := hposition.left_axis_strict
    dsimp [lower, upper]
    omega
  have hlowerPath : (![0, lower] : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    have haxis : (gamma.1.1 : Site 2) = ![0, lower] := by
      ext i
      fin_cases i <;> simp [lower, gamma.1.1.2.2]
    rw [← haxis]
    exact rlc_path_start_mem_vertices gamma.1
  have hupperPath : (![0, upper] : Site 2) ∈
      rlc_pathVertices gamma'.1 := by
    have haxis : (gamma'.1.2.1 : Site 2) = ![0, upper] := by
      ext i
      fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
    rw [← haxis]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hlower : (![0, lower] : Site 2) ∈ S :=
    rlc_rightPathVertex_mem_centralFaceReachSet
      gamma gamma' rho hlowerPath
  have hupper : (![0, upper] : Site 2) ∉ S :=
    rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
      gamma gamma' rho hno hupperPath
  let A : Finset Int := (Finset.Icc lower upper).filter
    (fun t => ![0, t] ∈ S)
  have hlowerA : lower ∈ A := by
    simp [A, hlower, le_of_lt hlowerLt]
  have hA : A.Nonempty := ⟨lower, hlowerA⟩
  let t := A.max' hA
  have htA : t ∈ A := A.max'_mem hA
  have htBounds : lower ≤ t ∧ t ≤ upper := by
    simpa [A] using (Finset.mem_filter.mp htA).1
  have htS : ![0, t] ∈ S := (Finset.mem_filter.mp htA).2
  have htlt : t < upper := by
    apply lt_of_le_of_ne htBounds.2
    intro h
    exact hupper (h ▸ htS)
  have habove : ∀ s : Int, t < s → s ≤ upper → ![0, s] ∉ S := by
    intro s hts hsu hsS
    have hsA : s ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, hsu⟩, hsS⟩
    have hmax := A.le_max' s hsA
    change s ≤ t at hmax
    omega
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htBounds.1, htlt, htS, habove,
    ⟨hadj, iff_of_true htS (habove (t + 1) (by omega) (by omega))⟩⟩


theorem rlc_centralFace_verticalGap_outside_mem_exterior {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceReachSet gamma gamma' rho ∧
      (∀ s : Int, t < s → s ≤ (gamma'.1.2.1 : Site 2) 1 →
        ![0, s] ∉ rlc_connectorCentralFaceReachSet gamma gamma' rho) ∧
      ![0, t + 1] ∈
        rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
  classical
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨t, htLower, htUpper, htIn, habove, _htBoundary⟩ :=
    rlc_centralFaceReachSet_verticalGap_outer_boundary_of_failure
      gamma gamma' hposition rho hno
  let upper := (gamma'.1.2.1 : Site 2) 1
  let leftStart := (gamma'.1.1 : Site 2)
  have hupperCoord : (![0, upper] : Site 2) = gamma'.1.2.1 := by
    ext i
    fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
  have hleftStartCoord : leftStart = ![-2 * n, leftStart 1] := by
    have hs := gamma'.1.1.2
    rw [mem_leftSide] at hs
    ext i
    fin_cases i <;> simp [leftStart, hs.2]
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box K
    (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)
  have hrightEndK : (gamma.1.2.1 : Site 2) ∈ K :=
    rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
      (rlc_connector_path_end_mem_vertices gamma.1)
  have hrightEndBox := hR hrightEndK
  have hrightEndX : (gamma.1.2.1 : Site 2) 0 = 2 * n := by
    exact gamma.1.2.1.2.2
  have hnR : 2 * n ≤ (R : Int) := by
    rw [mem_box] at hrightEndBox
    have h0 := hrightEndBox 0
    rw [hrightEndX] at h0
    have h0' : ((2 * n).natAbs : Int) ≤ (R : Int) := by
      exact_mod_cast h0
    exact le_trans Int.le_natAbs h0'
  let far : Site 2 := ![-((R : Int) + 1), 0]
  have hfarExt : far ∈ exterior 2 R := by
    simpa [far] using axisFarLeft_mem_exterior R
  have hfarNotK : far ∈ Kᶜ := exterior_subset_compl K R hR hfarExt
  let wAxis : (hypercubicLattice 2).Walk ![0, t + 1]
      (gamma'.1.2.1 : Site 2) :=
    (sw_vertSeg 0 (t + 1) upper).copy rfl hupperCoord
  let wLeft : (hypercubicLattice 2).Walk
      (gamma'.1.2.1 : Site 2) leftStart :=
    (rlc_ambientCrossingWalk gamma'.1).reverse
  let wHoriz : (hypercubicLattice 2).Walk leftStart
      ![-((R : Int) + 1), leftStart 1] :=
    (sw_horizSeg (leftStart 1) (-2 * n) (-((R : Int) + 1))).copy
      hleftStartCoord.symm rfl
  let wVert : (hypercubicLattice 2).Walk
      ![-((R : Int) + 1), leftStart 1] far :=
    (sw_vertSeg (-((R : Int) + 1)) (leftStart 1) 0).copy rfl rfl
  let w := ((wAxis.append wLeft).append wHoriz).append wVert
  have hwNot : ∀ z ∈ w.support, z ∈ Kᶜ := by
    intro z hz
    dsimp only [w] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with ((hzAxis | hzLeft) | hzHoriz) | hzVert
    · change z ∈ ((sw_vertSeg 0 (t + 1) upper).copy _ _).support at hzAxis
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzAxis
      obtain ⟨s, hs, rfl⟩ := hzAxis
      rw [Set.mem_uIcc, Or.comm] at hs
      rcases hs with hs | hs
      · exact habove s (by omega) (by omega)
      · exact habove s (by omega) (by omega)
    · have hzPath : z ∈ rlc_pathVertices gamma'.1 :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 z).1 (by
            simpa [wLeft, SimpleGraph.Walk.support_reverse] using hzLeft)
      exact rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno hzPath
    · change z ∈ ((sw_horizSeg (leftStart 1) (-2 * n)
          (-((R : Int) + 1))).copy _ _).support at hzHoriz
      rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hzHoriz
      obtain ⟨s, hs, rfl⟩ := hzHoriz
      rw [Set.mem_uIcc] at hs
      have hsle : s ≤ -2 * n := by
        rcases hs with hs | hs <;> omega
      intro hzK
      have hzRect := hzK.1
      rw [mem_rect] at hzRect
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzRect
      have hseq : s = -2 * n := by omega
      have hzEq : (![s, leftStart 1] : Site 2) = leftStart := by
        calc
          (![s, leftStart 1] : Site 2) = ![-2 * n, leftStart 1] := by
            rw [hseq]
          _ = leftStart := hleftStartCoord.symm
      rw [hzEq] at hzK
      exact (rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno (rlc_path_start_mem_vertices gamma'.1)) hzK
    · change z ∈ ((sw_vertSeg (-((R : Int) + 1))
          (leftStart 1) 0).copy _ _).support at hzVert
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hzVert
      obtain ⟨s, _hs, rfl⟩ := hzVert
      intro hzK
      have hzRect := hzK.1
      rw [mem_rect] at hzRect
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hzRect
      have hx := hzRect.1
      omega
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ ⟨far, hfarNotK⟩ := by
    exact ⟨w.induce Kᶜ hwNot⟩
  have hqInf : (((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩).supp.Infinite := by
    have hfarInf := exterior_mem_infiniteComponent
      (by norm_num) K R hR hfarExt
    have hcomp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ =
      ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
        ⟨far, hfarNotK⟩ := ConnectedComponent.sound hreach
    rwa [hcomp]
  have hqComp : ((hypercubicLattice 2).induce Kᶜ).connectedComponentMk
      ⟨![0, t + 1], hwNot _ w.start_mem_support⟩ =
        rlc_connectorCentralFaceExteriorComponent gamma gamma' rho :=
    (unique_infinite_component (by norm_num) K
      (rlc_connectorCentralFaceReachSet_finite gamma gamma' rho)).unique
        hqInf
        (rlc_connectorCentralFaceExteriorComponent_infinite gamma gamma' rho)
  exact ⟨t, htLower, htUpper, htIn, habove,
    ⟨hwNot _ w.start_mem_support, hqComp⟩⟩


theorem rlc_centralFaceFilled_verticalGap_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ t : Int,
      (gamma.1.1 : Site 2) 1 ≤ t ∧
      t < (gamma'.1.2.1 : Site 2) 1 ∧
      ![0, t] ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧
      ![0, t + 1] ∉
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho ∧
      ((![0, t], ![0, t + 1]) ∈ edgeBoundary 2
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  obtain ⟨t, htLower, htUpper, htIn, _habove, htOut⟩ :=
    rlc_centralFace_verticalGap_outside_mem_exterior
      gamma gamma' hposition rho hno
  have htFill := rlc_connectorCentralFaceReachSet_subset_filled
    gamma gamma' rho htIn
  have hsuccNotFill : ![0, t + 1] ∉
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using htOut
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htLower, htUpper, htFill, hsuccNotFill,
    ⟨hadj, iff_of_true htFill hsuccNotFill⟩⟩


end
end StatMech.Universality

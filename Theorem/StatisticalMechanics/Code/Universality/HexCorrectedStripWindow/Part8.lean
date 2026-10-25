/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSHeadingFin_eq_of_dvd_window {h k : ℤ}
    (hdvd : (6 : ℤ) ∣ h - k) :
    hexCSHeadingFin h = hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  change (h : ZMod 6) = (k : ZMod 6)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hdvd with ⟨q, hq⟩
  exact ⟨-q, by omega⟩

theorem hexCS_finalHeadingFin_eq_canonical
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexCSCanonicalHeading e) := by
  apply hexCSHeadingFin_eq_of_dvd_window
  apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
    (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
  exact hexCS_boundaryExitLaw T L hT e ts he hne hadm

theorem hexCSHeadingFin_four_window :
    hexCSHeadingFin 4 = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (4 : ZMod 6) = (4 : ZMod 6)
  rfl

theorem hexCSHeadingFin_neg_two_window :
    hexCSHeadingFin (-2) = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (-2 : ZMod 6) = (4 : ZMod 6)
  decide

theorem hexCSHeadingFin_three_window :
    hexCSHeadingFin 3 = 3 := by
  apply (ZMod.finEquiv 6).injective
  change (3 : ZMod 6) = (3 : ZMod 6)
  rfl

theorem hexCSHeadingFin_neg_one_window :
    hexCSHeadingFin (-1) = 5 := by
  apply (ZMod.finEquiv 6).injective
  change (-1 : ZMod 6) = (5 : ZMod 6)
  decide

theorem hexCS_boundaryBrickTurnLaw
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSWindowExteriorTurn e = 0 := by
  let R := hexCSBrickRadius T L
  let C := hexCSBrickDirections 1 ts
  let dx := (hexCSEndDelta e).1
  let dy := (hexCSEndDelta e).2
  have hR : 0 < R := by simp [R, hexCSBrickRadius]
  have hb := hexCSEndDelta_bounds (hT := hT) e he
  dsimp only at hb
  change (-(R : ℤ) < dx ∧ dx < R ∧
    -(R : ℤ) < dy ∧ dy < R) at hb
  have hC : C ≠ [] := hexCSBrickDirections_ne_nil 1 ts
  have hChead : C.head! = 2 := by
    simp [C, hexCSHeadingFin_one, hexBrickDir]
  have hmod := hexCS_finalHeadingFin_eq_canonical
    e ts he hne hadm
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, hdepth⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · have hdy : 0 < dy :=
        (hexCSEndDelta_left_sign e he hne hc hedge).1 hs
      have hE : 0 < (R : ℤ) + 1 - dx := by omega
      have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
        dsimp only [C]
        rw [hexCSBrickDirections_getLast, hmod,
          hexCSEastTail_head R dx hE]
        simp [hexCSCanonicalHeading, hc, hedge, hs,
          hexCSHeadingFin_four_window, hexBrickDir]
      have hsplit := hexCS_cyclicTurnSum_three_piece
        (hexCSSourceBelow R) C (hexCSEastTail R dx)
        (hexCSSourceBelow_ne_nil R hR) hC
        (hexCSEastTail_ne_nil R dx hE)
        (hexCSSourceBelow_head R hR)
        (hexCSSourceBelow_getLast R hR) hChead hjoin
        (hexCSEastTail_getLast R dx hE)
      have hz := hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
        e ts he hne hadm (Or.inl ⟨hc, hedge, hdepth⟩) hdy
      dsimp only at hz
      change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
      rw [hsplit, hexCSSourceBelow_openTurn R hR,
        hexCSEastTail_openTurn R dx] at hz
      simp [hexCSWindowExteriorTurn, hc, hedge, hs]
      omega
    · have hdy : dy < 0 :=
        (hexCSEndDelta_left_sign e he hne hc hedge).2 hs
      have hE : 0 < (R : ℤ) + 1 - dx := by omega
      have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
        dsimp only [C]
        rw [hexCSBrickDirections_getLast, hmod,
          hexCSEastTail_head R dx hE]
        simp [hexCSCanonicalHeading, hc, hedge, hs,
          hexCSHeadingFin_neg_two_window, hexBrickDir]
      have hsplit := hexCS_cyclicTurnSum_three_piece
        (hexCSSourceAbove R) C (hexCSEastTail R dx)
        (hexCSSourceAbove_ne_nil R hR) hC
        (hexCSEastTail_ne_nil R dx hE)
        (hexCSSourceAbove_head R hR)
        (hexCSSourceAbove_getLast R hR) hChead hjoin
        (hexCSEastTail_getLast R dx hE)
      have hz := hexCSAboveEastPeriod_cyclicTurnSum_eq_zero
        e ts he hne hadm ⟨hc, hedge, hdepth⟩ hdy
      dsimp only at hz
      change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
      rw [hsplit, hexCSSourceAbove_openTurn R hR,
        hexCSEastTail_openTurn R dx] at hz
      simp [hexCSWindowExteriorTurn, hc, hedge, hs]
      omega
  · rcases hright with ⟨hc, hedge, hdepth⟩
    have hW : 0 < dx + R := by omega
    have hN : 0 < (R : ℤ) - dy := by omega
    have hjoin : C.getLast! =
        (hexCSWestNorthEastTail R dx dy).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSWestNorthEastTail_head R dx dy hW]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_one, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceBelow R) C (hexCSWestNorthEastTail R dx dy)
      (hexCSSourceBelow_ne_nil R hR) hC
      (hexCSWestNorthEastTail_ne_nil R dx dy hW)
      (hexCSSourceBelow_head R hR)
      (hexCSSourceBelow_getLast R hR) hChead hjoin
      (hexCSWestNorthEastTail_getLast R dx dy)
    have hz := hexCSRightPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm ⟨hc, hedge, hdepth⟩
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceBelow_openTurn R hR,
      hexCSWestNorthEastTail_openTurn R dx dy hW hN] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega
  · rcases hupp with ⟨hc, hedge, hi⟩
    have hdy : 0 < dy :=
      (hexCSEndDelta_slant_sign e he).1 ⟨hc, hedge⟩
    have hE : 0 < (R : ℤ) + 1 - dx := by omega
    have hjoin : C.getLast! = (hexCSEastTail R dx).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSEastTail_head R dx hE]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_three_window, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceBelow R) C (hexCSEastTail R dx)
      (hexCSSourceBelow_ne_nil R hR) hC
      (hexCSEastTail_ne_nil R dx hE)
      (hexCSSourceBelow_head R hR)
      (hexCSSourceBelow_getLast R hR) hChead hjoin
      (hexCSEastTail_getLast R dx hE)
    have hz := hexCSBelowEastPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm (Or.inr ⟨hc, hedge, hi⟩) hdy
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceBelow_openTurn R hR,
      hexCSEastTail_openTurn R dx] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega
  · rcases hlow with ⟨hc, hedge, hj⟩
    have hdy : dy < 0 :=
      (hexCSEndDelta_slant_sign e he).2 ⟨hc, hedge⟩
    have hS : 0 < dy + R := by omega
    have hE : 0 < (R : ℤ) + 1 - dx := by omega
    have hE' : 0 < (R : ℤ) - dx := by omega
    have hjoin : C.getLast! =
        (hexCSSouthEastTail R dx dy).head! := by
      dsimp only [C]
      rw [hexCSBrickDirections_getLast, hmod,
        hexCSSouthEastTail_head R dx dy hS]
      simp [hexCSCanonicalHeading, hc, hedge,
        hexCSHeadingFin_neg_one_window, hexBrickDir]
    have hsplit := hexCS_cyclicTurnSum_three_piece
      (hexCSSourceAbove R) C (hexCSSouthEastTail R dx dy)
      (hexCSSourceAbove_ne_nil R hR) hC
      (hexCSSouthEastTail_ne_nil R dx dy hS)
      (hexCSSourceAbove_head R hR)
      (hexCSSourceAbove_getLast R hR) hChead hjoin
      (hexCSSouthEastTail_getLast R dx dy hE)
    have hz := hexCSLowerPeriod_cyclicTurnSum_eq_zero
      e ts he hne hadm ⟨hc, hedge, hj⟩
    dsimp only at hz
    change ons_openTurnSum C + hexCSWindowExteriorTurn e = 0
    rw [hsplit, hexCSSourceAbove_openTurn R hR,
      hexCSSouthEastTail_openTurn R dx dy hS hE'] at hz
    simp [hexCSWindowExteriorTurn, hc, hedge]
    omega

theorem hexCS_finalHeading_eq_canonical_of_window_turn
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (hperiod : ons_openTurnSum (hexCSBrickDirections 1 ts) +
      hexCSWindowExteriorTurn e = 0) :
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
  have htel := hexCS_brick_open_telescope 1 ts hadm.1.1
  have hmod := hexCS_finalHeadingFin_eq_canonical
    e ts he hne hadm
  have hhead : hexInfra_headAccum 1 ts = 1 + ts.sum := by
    rw [hexInfra_headAccum_eq_add_sum]
  rw [hmod] at htel
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge, hs,
        hexCSHeadingFin_four_window, hexBrickTurnPotential] at htel hperiod ⊢
      omega
    · simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge, hs,
        hexCSHeadingFin_neg_two_window, hexBrickTurnPotential] at htel hperiod ⊢
      omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hupp with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_three_window, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSWindowExteriorTurn, hc, hedge,
      hexCSHeadingFin_neg_one_window, hexBrickTurnPotential] at htel hperiod ⊢
    omega


theorem hexCS_boundaryWindowLaw (T L : ℕ) (hT : 0 < T) :
    HexCSBoundaryWindowLaw T L hT := by
  intro e ts he hne hadm
  have hperiod := hexCS_boundaryBrickTurnLaw e ts he hne hadm
  have hheading := hexCS_finalHeading_eq_canonical_of_window_turn
    e ts he hne hadm hperiod
  refine ⟨hexCSCanonicalHeading e, ?_⟩
  rw [hheading]
  omega

end
end StatMech.Universality

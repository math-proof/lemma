/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSHeadingFin_eq_of_dvd {h k : ℤ}
    (hdvd : (6 : ℤ) ∣ h - k) :
    hexCSHeadingFin h = hexCSHeadingFin k := by
  apply (ZMod.finEquiv 6).injective
  change (h : ZMod 6) = (k : ZMod 6)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  rcases hdvd with ⟨q, hq⟩
  exact ⟨-q, by omega⟩

theorem hexCSHeadingFin_four : hexCSHeadingFin 4 = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (4 : ZMod 6) = (4 : ZMod 6)
  rfl

theorem hexCSHeadingFin_neg_two : hexCSHeadingFin (-2) = 4 := by
  apply (ZMod.finEquiv 6).injective
  change (-2 : ZMod 6) = (4 : ZMod 6)
  decide

theorem hexCSHeadingFin_three : hexCSHeadingFin 3 = 3 := by
  apply (ZMod.finEquiv 6).injective
  change (3 : ZMod 6) = (3 : ZMod 6)
  rfl

theorem hexCSHeadingFin_neg_one : hexCSHeadingFin (-1) = 5 := by
  apply (ZMod.finEquiv 6).injective
  change (-1 : ZMod 6) = (5 : ZMod 6)
  decide


theorem hexCS_finalHeading_eq_canonical_of_tail_turn
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
      hexCSExteriorTailTurn e = 0) :
    hexInfra_headAccum 1 ts = hexCSCanonicalHeading e := by
  have htel := hexCS_brick_open_telescope 1 ts hadm.1.1
  have hexit := hexCS_boundaryExitLaw T L hT
  have hdvd : (6 : ℤ) ∣
      (hexInfra_headAccum 1 ts - hexCSCanonicalHeading e) := by
    apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
      (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
    exact hexit e ts he hne hadm
  have hmod : hexCSHeadingFin (hexInfra_headAccum 1 ts) =
      hexCSHeadingFin (hexCSCanonicalHeading e) :=
    hexCSHeadingFin_eq_of_dvd hdvd
  have hhead : hexInfra_headAccum 1 ts = 1 + ts.sum := by
    rw [hexInfra_headAccum_eq_add_sum]
  rw [hmod] at htel
  obtain hleft | hright | hupp | hlow :=
    hexCS_boundary_classification e he
  · rcases hleft with ⟨hc, hedge, _⟩
    by_cases hs : 0 ≤ hexAWTrans e.vtx.1
    · simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge, hs,
        hexCSHeadingFin_four, hexBrickTurnPotential] at htel hperiod ⊢
      omega
    · simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge, hs,
        hexCSHeadingFin_neg_two, hexBrickTurnPotential] at htel hperiod ⊢
      omega
  · rcases hright with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hupp with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_three, hexBrickTurnPotential] at htel hperiod ⊢
    omega
  · rcases hlow with ⟨hc, hedge, _⟩
    simp [hexCSCanonicalHeading, hexCSExteriorTailTurn, hc, hedge,
      hexCSHeadingFin_neg_one, hexBrickTurnPotential] at htel hperiod ⊢
    omega


end
end StatMech.Universality

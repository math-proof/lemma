/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Def.StatisticalMechanics.Code.Universality.HexAllWidthBoundaryWinding


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

theorem endpointCountWeight_nonneg (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ endpointCountWeight region a h0 z x ts := by
  unfold endpointCountWeight
  split <;> positivity


theorem endpointParafSummand_factor (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x W : ℝ) (ts : List ℤ)
    (hdet : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn region ∧
        (ofTurns a h0 ts).EndsAt z →
      (ofTurns a h0 ts).turning = W) :
    endpointParafSummand region a h0 z σ x ts =
      Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) *
        ((endpointCountWeight region a h0 z x ts : ℝ) : ℂ) := by
  unfold endpointParafSummand endpointCountWeight
  split_ifs with h
  · rw [hdet h]
    push_cast
    ring
  · push_cast
    ring


theorem endpointParafObservable_factor (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x W : ℝ)
    (hdet : ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt z →
        (ofTurns a h0 ts).turning = W) :
    endpointParafObservable region a h0 z σ x =
      Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) *
        ((endpointCountObservable region a h0 z x : ℝ) : ℂ) := by
  unfold endpointParafObservable endpointCountObservable
  rw [Complex.ofReal_tsum, ← tsum_mul_left]
  exact tsum_congr (fun ts =>
    endpointParafSummand_factor region a h0 z σ x W ts (hdet ts))


theorem endpointCountWeight_refl
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    endpointCountWeight region a h0 (hsc_refl a h0 z) x
        (hsc_negTurns ts) =
      endpointCountWeight region a h0 z x ts := by
  unfold endpointCountWeight
  have hiff := hsc_endpoint_admissible_refl_iff region a h0 z hsym ts
  by_cases h : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z
  · rw [if_pos (hiff.mpr h), if_pos h, hsc_genEndpointNumVertices]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]


theorem endpointCountObservable_refl
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
    endpointCountObservable region a h0 (hsc_refl a h0 z) x =
      endpointCountObservable region a h0 z x := by
  unfold endpointCountObservable
  rw [← Equiv.tsum_eq hsc_negEquiv
    (fun ts => endpointCountWeight region a h0 (hsc_refl a h0 z) x ts)]
  exact tsum_congr (endpointCountWeight_refl region a h0 z x hsym)


theorem endpoint_det_winding_reflect
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdet : ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt z →
        (ofTurns a h0 ts).turning = W) :
    ∀ ts,
      (ofTurns a h0 ts).EndpointIsLegalSAW ∧
          (ofTurns a h0 ts).StaysIn region ∧
          (ofTurns a h0 ts).EndsAt (hsc_refl a h0 z) →
        (ofTurns a h0 ts).turning = -W := by
  intro ts hadm
  have href :
      (ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW ∧
        (ofTurns a h0 (hsc_negTurns ts)).StaysIn region ∧
        (ofTurns a h0 (hsc_negTurns ts)).EndsAt z := by
    refine ⟨hsc_genEndpointIsLegalSAW a h0 ts hadm.1,
      hsc_genStaysIn region a h0 ts hsym hadm.2.1, ?_⟩
    unfold EndsAt at *
    rw [hsc_genEndMid, hadm.2.2, hsc_refl_invol]
  have hW := hdet (hsc_negTurns ts) href
  rw [hsc_genTurning_neg] at hW
  linarith


theorem hexAWNeighborPos_eq_mid_add (c : HexAWCoord) (e : Fin 3) :
    hexAWPos (hexAWNeighbor c e) =
      hexAWMid c e + halfStep (hexAWHeading c e) := by
  have hmid := hexAWMid_sub_pos c e
  have hpos := hexAWPos_neighbor c e
  calc
    hexAWPos (hexAWNeighbor c e) =
        hexAWPos c + hexUnit (hexAWHeading c e) := by
      linear_combination hpos
    _ = hexAWMid c e + (1 / 2 : ℂ) *
        hexUnit (hexAWHeading c e) := by
      have hmideq : hexAWMid c e = hexAWPos c +
          (1 / 2 : ℂ) * hexUnit (hexAWHeading c e) := by
        linear_combination hmid
      rw [hmideq]
      ring
    _ = hexAWMid c e + halfStep (hexAWHeading c e) := rfl


theorem hexAWEndpoint_finalHeading_mod
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge)) :
    (6 : ℤ) ∣
      (hexInfra_headAccum 1 ts - hexAWHeading e.vtx.1 e.edge) := by
  apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
    (hexAWMid e.vtx.1 e.edge) (hexAWHeading e.vtx.1 e.edge) ts hend
  rwa [hexAWNeighborPos_eq_mid_add] at hexit


theorem hexAWEndpoint_finalHeading_eq_of_window
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ) (w : ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
    (hwalkL : w ≤ hexInfra_headAccum 1 ts)
    (hwalkU : hexInfra_headAccum 1 ts < w + 6)
    (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
    (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
    hexInfra_headAccum 1 ts = hexAWHeading e.vtx.1 e.edge := by
  have hdvd := hexAWEndpoint_finalHeading_mod e ts hend hexit
  omega


theorem hexAWEndpoint_turning_eq_of_window
    {T L : ℕ} (e : HexAWIncidence T L) (ts : List ℤ) (w : ℤ)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt
      (hexAWMid e.vtx.1 e.edge))
    (hexit : hexInfra_midAccum hexAWStart 1 ts +
        halfStep (hexInfra_headAccum 1 ts) =
      hexAWPos (hexAWNeighbor e.vtx.1 e.edge))
    (hwalkL : w ≤ hexInfra_headAccum 1 ts)
    (hwalkU : hexInfra_headAccum 1 ts < w + 6)
    (hedgeL : w ≤ hexAWHeading e.vtx.1 e.edge)
    (hedgeU : hexAWHeading e.vtx.1 e.edge < w + 6) :
    (ofTurns hexAWStart 1 ts).turning =
      (Real.pi / 3) * ((hexAWHeading e.vtx.1 e.edge : ℝ) - 1) := by
  simpa only [Int.cast_one] using
    (hexInfra_turning_const_of_finalHeading hexAWStart 1 ts
      (hexAWHeading e.vtx.1 e.edge)
      (hexAWEndpoint_finalHeading_eq_of_window e ts w hend hexit
        hwalkL hwalkU hedgeL hedgeU))


end
end StatMech.Universality

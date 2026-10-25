/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Def.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hsc_cw_refl (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    hexClosed_cw region a h0 (hsc_refl a h0 z) x (hsc_negTurns ts)
      = hexClosed_cw region a h0 z x ts := by
  unfold hexClosed_cw
  have hnum : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).numVertices
      = (HexWalk.ofTurns a h0 ts).numVertices := hsc_genNumVertices a h0 ts
  have hiff : ((HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region
        ∧ (HexWalk.ofTurns a h0 (hsc_negTurns ts)).EndsAt (hsc_refl a h0 z))
      ↔ ((HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z) := by
    constructor
    · rintro ⟨⟨hlt, hsaw⟩, hstays, hends⟩
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · have := hsc_genLegalTurns a h0 (hsc_negTurns ts) hlt
        rwa [hsc_negTurns_negTurns] at this
      · have := hsc_genIsSAW a h0 (hsc_negTurns ts) hsaw
        rwa [hsc_negTurns_negTurns] at this
      · have := hsc_genStaysIn region a h0 (hsc_negTurns ts) hsym hstays
        rwa [hsc_negTurns_negTurns] at this
      · unfold HexWalk.EndsAt at *
        rw [hsc_genEndMid] at hends
        exact hsc_refl_injective a h0 hends
    · rintro ⟨⟨hlt, hsaw⟩, hstays, hends⟩
      refine ⟨⟨hsc_genLegalTurns a h0 ts hlt, hsc_genIsSAW a h0 ts hsaw⟩,
        hsc_genStaysIn region a h0 ts hsym hstays, ?_⟩
      unfold HexWalk.EndsAt at *
      rw [hsc_genEndMid, hends]
  by_cases h : (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z
  · rw [if_pos (hiff.mpr h), if_pos h, hnum]
  · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h]


theorem hsc_countObs_refl (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
    hexClosed_countObs region a h0 (hsc_refl a h0 z) x
      = hexClosed_countObs region a h0 z x := by
  unfold hexClosed_countObs
  rw [← Equiv.tsum_eq hsc_negEquiv (fun ts => hexClosed_cw region a h0 (hsc_refl a h0 z) x ts)]
  exact tsum_congr (fun ts => hsc_cw_refl region a h0 z x hsym ts)


theorem hsc_detb_of_dett (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt (hsc_refl a h0 z)
          → (HexWalk.ofTurns a h0 ts).turning = -W := by
  rintro ts ⟨⟨hlt, hsaw⟩, hstays, hends⟩
  have hlt' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).LegalTurns := hsc_genLegalTurns a h0 ts hlt
  have hsaw' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsSAW := hsc_genIsSAW a h0 ts hsaw
  have hstays' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region :=
    hsc_genStaysIn region a h0 ts hsym hstays
  have hends' : (HexWalk.ofTurns a h0 (hsc_negTurns ts)).EndsAt z := by
    unfold HexWalk.EndsAt at hends ⊢
    rw [hsc_genEndMid, hends, hsc_refl_invol]
  have hW := hdett (hsc_negTurns ts) ⟨⟨hlt', hsaw'⟩, hstays', hends'⟩
  rw [hsc_genTurning_neg] at hW
  linarith


theorem hsc_sidePhaseLock_single (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (σ x W : ℝ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m))
    (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
    parafObservable region a h0 z σ x
        + parafObservable region a h0 (hsc_refl a h0 z) σ x
      = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) :=
  hexClosed_sidePhaseLock_of_reflection region a h0 z (hsc_refl a h0 z) σ x W
    (hexClosed_countObs region a h0 z x) hdett
    (hsc_detb_of_dett region a h0 z W hsym hdett) rfl
    (hsc_countObs_refl region a h0 z x hsym)


theorem hsc_full_region_sym (a : ℂ) (h0 : ℤ) :
    ∀ m, (fun _ : ℂ => True) m → (fun _ : ℂ => True) (hsc_refl a h0 m) :=
  fun _ _ => trivial


theorem hsc_countObs_refl_full (a : ℂ) (h0 : ℤ) (z : ℂ) (x : ℝ) :
    hexClosed_countObs (fun _ => True) a h0 (hsc_refl a h0 z) x
      = hexClosed_countObs (fun _ => True) a h0 z x :=
  hsc_countObs_refl (fun _ => True) a h0 z x (hsc_full_region_sym a h0)


theorem hsc_sidePhaseLock_zeroWinding (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (hdet0 : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW
        ∧ (HexWalk.ofTurns a h0 ts).StaysIn (fun _ => True)
        ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = 0) :
    parafObservable (fun _ => True) a h0 z σ x
        + parafObservable (fun _ => True) a h0 (hsc_refl a h0 z) σ x
      = ((2 * hexClosed_countObs (fun _ => True) a h0 z x : ℝ) : ℂ) := by
  have h := hsc_sidePhaseLock_single (fun _ => True) a h0 z σ x 0 (hsc_full_region_sym a h0) hdet0
  rw [mul_zero, Real.cos_zero] at h
  rw [h]; push_cast; ring

end StatMech.Universality

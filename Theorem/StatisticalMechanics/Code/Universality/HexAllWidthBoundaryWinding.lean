/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthBoundaryWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripOrbits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

noncomputable section

theorem hsc_genEndpointVertices (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (hsc_negTurns ts)).endpointVertices =
      (ofTurns a h0 ts).endpointVertices.map (hsc_refl a h0) := by
  unfold endpointVertices vertices
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns]
  have hverts := hsc_genVerticesAux a h0 a h0 ts
  have hfix : hsc_refl a h0 a = a := hsc_refl_fixed a h0
  have hhead : 2 * h0 - h0 = h0 := by ring
  rw [hfix, hhead] at hverts
  rw [hverts]
  have map_dropLast (l : List ℂ) :
      (l.map (hsc_refl a h0)).dropLast =
        l.dropLast.map (hsc_refl a h0) := by
    induction l with
    | nil => simp
    | cons x xs =>
        cases xs with
        | nil => simp
        | cons y ys => simp_all
  exact map_dropLast _


theorem hsc_genEndpointIsSAW (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW) :
    (ofTurns a h0 (hsc_negTurns ts)).EndpointIsSAW := by
  unfold EndpointIsSAW at *
  rw [hsc_genEndpointVertices]
  exact hsaw.map (hsc_refl_injective a h0)


theorem hsc_genEndpointIsLegalSAW (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW) :
    (ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW :=
  ⟨hsc_genLegalTurns a h0 ts hlegal.1,
    hsc_genEndpointIsSAW a h0 ts hlegal.2⟩


@[simp] theorem hsc_genEndpointNumVertices (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) :
    (ofTurns a h0 (hsc_negTurns ts)).endpointNumVertices =
      (ofTurns a h0 ts).endpointNumVertices := by
  simp [endpointNumVertices, hsc_negTurns]


theorem hsc_endpoint_admissible_refl_iff
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ)
    (hsym : ∀ m, region m → region (hsc_refl a h0 m)) (ts : List ℤ) :
    ((ofTurns a h0 (hsc_negTurns ts)).EndpointIsLegalSAW ∧
        (ofTurns a h0 (hsc_negTurns ts)).StaysIn region ∧
        (ofTurns a h0 (hsc_negTurns ts)).EndsAt (hsc_refl a h0 z)) ↔
      ((ofTurns a h0 ts).EndpointIsLegalSAW ∧
        (ofTurns a h0 ts).StaysIn region ∧
        (ofTurns a h0 ts).EndsAt z) := by
  constructor
  · rintro ⟨hlegal, hstay, hend⟩
    have hlegal' := hsc_genEndpointIsLegalSAW a h0 (hsc_negTurns ts) hlegal
    have hstay' := hsc_genStaysIn region a h0 (hsc_negTurns ts) hsym hstay
    refine ⟨?_, ?_, ?_⟩
    · rw [hsc_negTurns_negTurns] at hlegal'
      exact hlegal'
    · rw [hsc_negTurns_negTurns] at hstay'
      exact hstay'
    · unfold EndsAt at *
      rw [hsc_genEndMid] at hend
      exact hsc_refl_injective a h0 hend
  · rintro ⟨hlegal, hstay, hend⟩
    refine ⟨hsc_genEndpointIsLegalSAW a h0 ts hlegal,
      hsc_genStaysIn region a h0 ts hsym hstay, ?_⟩
    unfold EndsAt at *
    rw [hsc_genEndMid, hend]


end
end StatMech.Universality

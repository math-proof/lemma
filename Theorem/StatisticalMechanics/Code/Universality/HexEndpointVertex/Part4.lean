/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part4


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem endpointParafSummand_eq_zero_of_not_endsAt
    (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ)
    (ts : List ℤ) (hne : ¬(ofTurns a h0 ts).EndsAt z) :
    endpointParafSummand region a h0 z σ x ts = 0 := by
  unfold endpointParafSummand
  rw [if_neg]
  exact fun h => hne h.2.2


theorem endpointCombinedSummand_at_p
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + du) - v) *
        endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega * du) _ _ ts
      (fun h => hexMid_p_ne_q hdu (hend.symm.trans h)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega ^ 2 * du) _ _ ts
      (fun h => hexMid_p_ne_r hdu (hend.symm.trans h))]
  ring


theorem endpointCombinedSummand_at_q
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega * du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + du) _ _ ts (fun h => hexMid_p_ne_q hdu (h.symm.trans hend)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega ^ 2 * du) _ _ ts
      (fun h => hexMid_q_ne_r hdu (hend.symm.trans h))]
  ring


theorem endpointCombinedSummand_at_r
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du)) :
    endpointCombinedSummand region a h0 v du ts =
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts := by
  unfold endpointCombinedSummand
  rw [endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + du) _ _ ts (fun h => hexMid_p_ne_r hdu (h.symm.trans hend)),
    endpointParafSummand_eq_zero_of_not_endsAt region a h0
      (v + hexOmega * du) _ _ ts
      (fun h => hexMid_q_ne_r hdu (h.symm.trans hend))]
  ring


@[simp] theorem endpointParafSummand_nil (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (σ x : ℝ) (ha : region a) :
    endpointParafSummand region a h0 a σ x [] = 1 := by
  unfold endpointParafSummand
  rw [if_pos]
  · simp [endpointNumVertices, turning, turnCount]
  · refine ⟨endpoint_nil_isLegalSAW a h0, ?_, ?_⟩
    · intro m hm
      have : m = a := by simpa [mids, ofTurns] using hm
      simpa [this] using ha
    · exact trivialWalk_endMid a h0


theorem endpointContribution_eq_summand (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z v : ℂ) (ts : List ℤ)
    (hcond : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z) :
    (z - v) * endpointParafSummand region a h0 z (5 / 8) hexChi ts =
      hexContribution (z - v) (ofTurns a h0 ts).turnCount
        (ofTurns a h0 ts).endpointNumVertices := by
  unfold endpointParafSummand hexContribution
  rw [if_pos hcond, ← hexPhase_eq_lambda_zpow (ofTurns a h0 ts)]
  ring


theorem endpointParafSummand_guard_of_ne (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ)
    (hne : endpointParafSummand region a h0 z σ x ts ≠ 0) :
    (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt z := by
  unfold endpointParafSummand at hne
  by_contra hguard
  rw [if_neg hguard] at hne
  exact hne rfl


namespace HexFiniteRegion

variable (R : HexFiniteRegion)


theorem endpointLength_le (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).EndpointIsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn R.inRegion) :
    ts.length ≤ R.verts.card := by
  classical
  have hmem : ∀ y ∈ (ofTurns a h0 ts).endpointVertices, y ∈ R.verts := by
    intro y hy
    apply R.vertices_mem a h0 ts hstay y
    exact (List.dropLast_sublist _).mem hy
  have hsub : (ofTurns a h0 ts).endpointVertices.toFinset ⊆ R.verts := by
    intro y hy
    exact hmem y (List.mem_toFinset.mp hy)
  calc
    ts.length = (ofTurns a h0 ts).endpointVertices.length := by
      simp [endpointNumVertices]
    _ = (ofTurns a h0 ts).endpointVertices.toFinset.card :=
      (List.toFinset_card_of_nodup hsaw).symm
    _ ≤ R.verts.card := Finset.card_le_card hsub


theorem endpointParaf_support_subset_boundedLegal
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Function.support (endpointParafSummand R.inRegion a h0 z σ x) ⊆
      {ts : List ℤ |
        (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
  intro ts hts
  have hg := endpointParafSummand_guard_of_ne R.inRegion a h0 z σ x ts hts
  exact ⟨hg.1.1, R.endpointLength_le a h0 ts hg.1.2 hg.2.1⟩


theorem endpointParaf_support_finite
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    (Function.support
      (endpointParafSummand R.inRegion a h0 z σ x)).Finite :=
  Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
    (R.endpointParaf_support_subset_boundedLegal a h0 z σ x)


theorem endpointParaf_summable
    (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Summable (endpointParafSummand R.inRegion a h0 z σ x) := by
  let S := (R.endpointParaf_support_finite a h0 z σ x).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro ts hts
  by_contra hne
  apply hts
  change ts ∈ (R.endpointParaf_support_finite a h0 z σ x).toFinset
  simpa [S] using hne


theorem endpointCombined_support_valid (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn R.inRegion := by
  have hor :
      endpointParafSummand R.inRegion a h0 (v + du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts ≠ 0 := by
    by_contra hall
    simp only [not_or] at hall
    apply hne
    unfold endpointCombinedSummand
    rw [not_ne_iff.mp hall.1, not_ne_iff.mp hall.2.1,
      not_ne_iff.mp hall.2.2]
    ring
  rcases hor with hp | hq | hr
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + du) (5 / 8) hexChi ts hp
    exact ⟨h.1, h.2.1⟩
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega * du) (5 / 8) hexChi ts hq
    exact ⟨h.1, h.2.1⟩
  · have h := endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega ^ 2 * du) (5 / 8) hexChi ts hr
    exact ⟨h.1, h.2.1⟩


theorem endpointCombined_support_endsAt (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hne : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    (ofTurns a h0 ts).EndsAt (v + du) ∨
      (ofTurns a h0 ts).EndsAt (v + hexOmega * du) ∨
      (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
  have hor :
      endpointParafSummand R.inRegion a h0 (v + du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi ts ≠ 0 ∨
        endpointParafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi ts ≠ 0 := by
    by_contra hall
    simp only [not_or] at hall
    apply hne
    unfold endpointCombinedSummand
    rw [not_ne_iff.mp hall.1, not_ne_iff.mp hall.2.1,
      not_ne_iff.mp hall.2.2]
    ring
  rcases hor with hp | hq | hr
  · exact Or.inl (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + du) (5 / 8) hexChi ts hp).2.2
  · exact Or.inr (Or.inl (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega * du) (5 / 8) hexChi ts hq).2.2)
  · exact Or.inr (Or.inr (endpointParafSummand_guard_of_ne R.inRegion a h0
      (v + hexOmega ^ 2 * du) (5 / 8) hexChi ts hr).2.2)


theorem endpointCombined_support_finite (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    (Function.support
      (endpointCombinedSummand R.inRegion a h0 v du)).Finite := by
  apply Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
  intro ts hts
  have h := R.endpointCombined_support_valid a h0 v du ts hts
  exact ⟨h.1.1, R.endpointLength_le a h0 ts h.1.2 h.2⟩


end HexFiniteRegion
end
end StatMech.Universality

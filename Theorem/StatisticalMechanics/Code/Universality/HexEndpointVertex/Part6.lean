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
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part6


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

namespace HexFiniteRegion

variable (R : HexFiniteRegion)


@[simp] theorem mem_endpointVisitClassFinset
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (k : ℕ) (ts : List ℤ) :
    ts ∈ R.endpointVisitClassFinset a h0 v du k ↔
      endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0 ∧
        specialMidCount a h0 v du ts = k := by
  simp [endpointVisitClassFinset]


theorem endpointSupport_specialMidCount_pos
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    0 < specialMidCount a h0 v du ts := by
  classical
  rcases R.endpointCombined_support_endsAt a h0 v du ts hts with hp | hq | hr
  · have hm := hexClass_endsAt_passesThrough ts (v + du) hp
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega
  · have hm := hexClass_endsAt_passesThrough ts (v + hexOmega * du) hq
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega
  · have hm := hexClass_endsAt_passesThrough ts (v + hexOmega ^ 2 * du) hr
    unfold specialMidCount
    rw [if_pos hm]
    split <;> split <;> omega


theorem endpointSupport_specialMidCount_cases
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hts : endpointCombinedSummand R.inRegion a h0 v du ts ≠ 0) :
    specialMidCount a h0 v du ts = 1 ∨
      specialMidCount a h0 v du ts = 2 ∨
      specialMidCount a h0 v du ts = 3 := by
  have hlo := R.endpointSupport_specialMidCount_pos a h0 v du ts hts
  have hhi := specialMidCount_le_three a h0 v du ts
  omega

theorem endpointSupportFinset_eq_visitClasses
    (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    R.endpointCombinedSupportFinset a h0 v du =
      R.endpointVisitClassFinset a h0 v du 1 ∪
        R.endpointVisitClassFinset a h0 v du 2 ∪
        R.endpointVisitClassFinset a h0 v du 3 := by
  ext ts
  constructor
  · intro hts
    have hs := (R.mem_endpointCombinedSupportFinset a h0 v du ts).mp hts
    rcases R.endpointSupport_specialMidCount_cases a h0 v du ts hs with
      h1 | h2 | h3
    · simp [mem_endpointVisitClassFinset, hs, h1]
    · simp [mem_endpointVisitClassFinset, hs, h2]
    · simp [mem_endpointVisitClassFinset, hs, h3]
  · intro hts
    simp only [Finset.mem_union, mem_endpointVisitClassFinset] at hts
    rcases hts with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;>
      exact (R.mem_endpointCombinedSupportFinset a h0 v du ts).2 h

theorem endpointVisitClassFinset_disjoint
    (a : ℂ) (h0 : ℤ) (v du : ℂ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (R.endpointVisitClassFinset a h0 v du k)
      (R.endpointVisitClassFinset a h0 v du l) := by
  rw [Finset.disjoint_left]
  intro ts hk hl
  have hk' := ((R.mem_endpointVisitClassFinset a h0 v du k ts).mp hk).2
  have hl' := ((R.mem_endpointVisitClassFinset a h0 v du l ts).mp hl).2
  exact hkl (hk'.symm.trans hl')

end HexFiniteRegion


theorem endpointVertexSum_eq_tsum_combined
    (R : HexFiniteRegion) (a : ℂ) (h0 : ℤ) (v du : ℂ) :
    ((v + du) - v) *
        endpointParafObservable R.inRegion a h0 (v + du)
          (5 / 8) hexChi +
      ((v + hexOmega * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega * du)
          (5 / 8) hexChi +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafObservable R.inRegion a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi =
      ∑' ts, endpointCombinedSummand R.inRegion a h0 v du ts := by
  unfold endpointParafObservable endpointCombinedSummand
  have hp := R.endpointParaf_summable a h0 (v + du) (5 / 8) hexChi
  have hq := R.endpointParaf_summable a h0
    (v + hexOmega * du) (5 / 8) hexChi
  have hr := R.endpointParaf_summable a h0
    (v + hexOmega ^ 2 * du) (5 / 8) hexChi
  rw [← hp.tsum_mul_left, ← hq.tsum_mul_left, ← hr.tsum_mul_left]
  rw [← (hp.mul_left _).tsum_add (hq.mul_left _),
    ← ((hp.mul_left _).add (hq.mul_left _)).tsum_add (hr.mul_left _)]

@[simp] theorem endpointNumVertices_append_one (a : ℂ) (h0 t : ℤ)
    (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).endpointNumVertices =
      (ofTurns a h0 ts).endpointNumVertices + 1 := by
  simp [endpointNumVertices]


theorem endpoint_genuine_triplet_zero (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (ts : List ℤ)
    (hp : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt (v + du))
    (hq : (ofTurns a h0 (ts ++ [-1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (ts ++ [-1])).StaysIn region ∧
      (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (ts ++ [1])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (ts ++ [1])).StaysIn region ∧
      (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + du) - v) *
        endpointParafSummand region a h0 (v + du) (5 / 8) hexChi ts +
      ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (ts ++ [-1]) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (ts ++ [1]) = 0 := by
  rw [endpointContribution_eq_summand region a h0 (v + du) v ts hp,
    endpointContribution_eq_summand region a h0 (v + hexOmega * du) v
      (ts ++ [-1]) hq,
    endpointContribution_eq_summand region a h0 (v + hexOmega ^ 2 * du) v
      (ts ++ [1]) hr,
    turnCount_concat a h0 (-1) ts, turnCount_concat a h0 1 ts,
    endpointNumVertices_append_one a h0 (-1) ts,
    endpointNumVertices_append_one a h0 1 ts]
  simp only [add_sub_cancel_left]
  have key := hexTripletContribution_zero du
    (ofTurns a h0 ts).turnCount (ofTurns a h0 ts).endpointNumVertices
  have hm : (ofTurns a h0 ts).turnCount + (-1 : ℤ) =
      (ofTurns a h0 ts).turnCount - 1 := by ring
  rw [hm]
  exact key


theorem endpoint_genuine_pair_zero (region : ℂ → Prop) (a : ℂ)
    (h0 : ℤ) (v du : ℂ) (base Lq Lr : List ℤ)
    (hLqsum : Lq.sum = -4) (hLrsum : Lr.sum = 4)
    (hlen : Lq.length = Lr.length)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ Lr)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lr)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ Lr) = 0 := by
  rw [endpointContribution_eq_summand region a h0 (v + hexOmega * du) v
      (base ++ Lq) hq,
    endpointContribution_eq_summand region a h0 (v + hexOmega ^ 2 * du) v
      (base ++ Lr) hr,
    turnCount_append_block a h0 base Lq,
    turnCount_append_block a h0 base Lr, hLqsum, hLrsum]
  have hnq : (ofTurns a h0 (base ++ Lq)).endpointNumVertices =
      (ofTurns a h0 base).endpointNumVertices + Lq.length := by
    simp [endpointNumVertices]
  have hnr : (ofTurns a h0 (base ++ Lr)).endpointNumVertices =
      (ofTurns a h0 base).endpointNumVertices + Lr.length := by
    simp [endpointNumVertices]
  rw [hnq, hnr, ← hlen]
  simp only [add_sub_cancel_left]
  have key := hexPairContribution_zero du (ofTurns a h0 base).turnCount
    ((ofTurns a h0 base).endpointNumVertices + Lq.length)
  have hm : (ofTurns a h0 base).turnCount + (-4 : ℤ) =
      (ofTurns a h0 base).turnCount - 4 := by ring
  rw [hm]
  exact key

theorem endpoint_genuine_pair_zero_via_reversal (region : ℂ → Prop)
    (a : ℂ) (h0 : ℤ) (v du : ℂ) (base Lq : List ℤ)
    (hLqsum : Lq.sum = -4)
    (hq : (ofTurns a h0 (base ++ Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ loopReverse Lq)).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ loopReverse Lq)).StaysIn region ∧
      (ofTurns a h0 (base ++ loopReverse Lq)).EndsAt
        (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega * du)
          (5 / 8) hexChi (base ++ Lq) +
      ((v + hexOmega ^ 2 * du) - v) *
        endpointParafSummand region a h0 (v + hexOmega ^ 2 * du)
          (5 / 8) hexChi (base ++ loopReverse Lq) = 0 :=
  endpoint_genuine_pair_zero region a h0 v du base Lq (loopReverse Lq)
    hLqsum (by rw [loopReverse_sum, hLqsum]; ring)
    (loopReverse_length Lq).symm hq hr


end
end StatMech.Universality

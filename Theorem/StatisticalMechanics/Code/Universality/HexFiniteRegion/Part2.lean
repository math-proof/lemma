/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexVertexClassification.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexFinite_boundedLegal_finite (N : ℕ) :
    {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ N}.Finite := by
  have hfin : {l : List Bool | l.length ≤ N}.Finite := List.finite_length_le Bool N
  apply Set.Finite.of_finite_image (f := hexFiniteEnc) _ ?_
  · apply hfin.subset
    rintro b ⟨ts, ⟨_, hlen⟩, rfl⟩
    simp only [Set.mem_setOf_eq, hexFiniteEnc, List.length_map]
    exact hlen
  · rintro ts1 ⟨h1, _⟩ ts2 ⟨h2, _⟩ heq
    simp only [hexFiniteEnc] at heq
    apply List.ext_getElem
    · have := congrArg List.length heq; simpa using this
    · intro n hn1 hn2
      have hget := congrArg (fun l => l[n]?) heq
      simp only [List.getElem?_map] at hget
      have hm1 := h1 ts1[n] (List.getElem_mem hn1)
      have hm2 := h2 ts2[n] (List.getElem_mem hn2)
      rcases hm1 with ha | ha <;> rcases hm2 with hb | hb <;> simp_all

namespace HexFiniteRegion

variable (R : HexFiniteRegion)


variable {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem support_isLegalSAW_staysIn (hdu : du ≠ 0) (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand R.inRegion a h0 v du)) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn R.inRegion := by
  rcases support_endsAt_threeMid (region := R.inRegion) ts h with hp | hq | hr
  · exact support_isLegalSAW ts h hp hdu
  · have hcs := combinedSummand_at_q (region := R.inRegion) hdu hq
    have hne : parafSummand R.inRegion a h0 (v + hexOmega * du) (5/8) hexChi ts ≠ 0 := by
      intro hz; apply h
      show combinedSummand R.inRegion a h0 v du ts = 0
      rw [hcs, hz, mul_zero]
    unfold parafSummand at hne
    by_contra hcon
    rw [not_and_or] at hcon
    apply hne; rw [if_neg]
    rintro ⟨h1, h2, _⟩
    rcases hcon with h1' | h2'
    · exact h1' h1
    · exact h2' h2
  · have hcs := combinedSummand_at_r (region := R.inRegion) hdu hr
    have hne : parafSummand R.inRegion a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts ≠ 0 := by
      intro hz; apply h
      show combinedSummand R.inRegion a h0 v du ts = 0
      rw [hcs, hz, mul_zero]
    unfold parafSummand at hne
    by_contra hcon
    rw [not_and_or] at hcon
    apply hne; rw [if_neg]
    rintro ⟨h1, h2, _⟩
    rcases hcon with h1' | h2'
    · exact h1' h1
    · exact h2' h2


theorem support_subset_boundedLegal (hdu : du ≠ 0) :
    Function.support (combinedSummand R.inRegion a h0 v du) ⊆
      {ts : List ℤ | (∀ t ∈ ts, t = 1 ∨ t = -1) ∧ ts.length ≤ R.verts.card} := by
  intro ts hts
  obtain ⟨hlegal, hstay⟩ := R.support_isLegalSAW_staysIn hdu ts hts
  obtain ⟨hturns, hsaw⟩ := hlegal
  refine ⟨?_, ?_⟩
  · intro t ht
    have := hturns t (by simpa using ht)
    exact this
  · exact le_of_lt (R.length_lt a h0 ts hsaw hstay)


theorem support_finite (hdu : du ≠ 0) :
    (Function.support (combinedSummand R.inRegion a h0 v du)).Finite :=
  Set.Finite.subset (hexFinite_boundedLegal_finite R.verts.card)
    (R.support_subset_boundedLegal hdu)


end HexFiniteRegion
end StatMech.Universality

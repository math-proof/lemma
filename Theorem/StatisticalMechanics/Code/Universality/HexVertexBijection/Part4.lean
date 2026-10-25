/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexBijection.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hlabel_tripletOnly (E : HexVertexEnumeration region a h0 v du)
    (hnopairs : E.pairs = ∅)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P, _⟩ | ⟨T1, i1⟩) s2 hlab hst
  · exact absurd (hnopairs ▸ P.2 : (P : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
  · rcases s2 with (⟨P, _⟩ | ⟨T2, i2⟩)
    · exact absurd (hnopairs ▸ P.2 : (P : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
    · match i1, i2 with
      | ⟨0, _⟩, ⟨0, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨1, _⟩, ⟨1, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := (List.append_left_inj _).mp hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨2, _⟩, ⟨2, _⟩ =>
        have hb : E.tripBase T1 = E.tripBase T2 := (List.append_left_inj _).mp hst
        have := htinj T1 T2 hb; subst this; rfl
      | ⟨0, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab
      | ⟨0, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab


theorem hinj_tripletOnly (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hnopairs : E.pairs = ∅)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_tripletOnly E hnopairs htinj)


theorem hlabel_pairOnly (E : HexVertexEnumeration region a h0 v du)
    (hnotrip : E.triplets = ∅)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P1, b1⟩ | ⟨T, _⟩) s2 hlab hst
  · rcases s2 with (⟨P2, b2⟩ | ⟨T, _⟩)
    · cases b1 <;> cases b2
      · have := hqinj P1 P2 hst; subst this; rfl
      · simp [slotLabel] at hlab
      · simp [slotLabel] at hlab
      · have := hrinj P1 P2 hst; subst this; rfl
    · exact absurd (hnotrip ▸ T.2 : (T : ℕ) ∈ (∅ : Finset ℕ)) (by simp)
  · exact absurd (hnotrip ▸ T.2 : (T : ℕ) ∈ (∅ : Finset ℕ)) (by simp)


theorem hinj_pairOnly (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hnotrip : E.triplets = ∅)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_pairOnly E hnotrip hqinj hrinj)


theorem hlabel_general (E : HexVertexEnumeration region a h0 v du)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
    ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2 := by
  rintro (⟨P1, b1⟩ | ⟨T1, i1⟩) (⟨P2, b2⟩ | ⟨T2, i2⟩) hlab hst
  · cases b1 <;> cases b2
    · have := hqinj P1 P2 hst; subst this; rfl
    · simp [slotLabel] at hlab
    · simp [slotLabel] at hlab
    · have := hrinj P1 P2 hst; subst this; rfl
  · cases b1
    · match i2 with
      | ⟨1, _⟩ => exact absurd hst (hqcross P1 T2)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩ => simp [slotLabel] at hlab
    · match i2 with
      | ⟨2, _⟩ => exact absurd hst (hrcross P1 T2)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩ => simp [slotLabel] at hlab
  · cases b2
    · match i1 with
      | ⟨1, _⟩ => exact absurd hst.symm (hqcross P2 T1)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨2, _⟩ => simp [slotLabel] at hlab
    · match i1 with
      | ⟨2, _⟩ => exact absurd hst.symm (hrcross P2 T1)
      | ⟨0, _⟩ => simp [slotLabel] at hlab
      | ⟨1, _⟩ => simp [slotLabel] at hlab
  · match i1, i2 with
    | ⟨0, _⟩, ⟨0, _⟩ => have := htinj T1 T2 hst; subst this; rfl
    | ⟨1, _⟩, ⟨1, _⟩ => have := htinj T1 T2 ((List.append_left_inj _).mp hst); subst this; rfl
    | ⟨2, _⟩, ⟨2, _⟩ => have := htinj T1 T2 ((List.append_left_inj _).mp hst); subst this; rfl
    | ⟨0, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab
    | ⟨0, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
    | ⟨1, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
    | ⟨1, _⟩, ⟨2, _⟩ => simp [slotLabel] at hlab
    | ⟨2, _⟩, ⟨0, _⟩ => simp [slotLabel] at hlab
    | ⟨2, _⟩, ⟨1, _⟩ => simp [slotLabel] at hlab


theorem hinj_general (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1]) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 :=
  hinj_of_perLabel E hdu (hlabel_general E htinj hqinj hrinj hqcross hrcross)


theorem hsub_of_coverage (E : HexVertexEnumeration region a h0 v du)
    (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts) :
    Function.support (combinedSummand region a h0 v du) ⊆
      Set.range fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  intro ts hts
  have hslot : ∃ slot : SlotType E, E.slotTurns slot = ts := by
    rcases support_endsAt_threeMid ts hts with hp | hq | hr
    · exact covp ts hts hp
    · exact covq ts hts hq
    · exact covr ts hts hr
  obtain ⟨slot, hsl⟩ := hslot
  have hmem : slot ∈ Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) := by
    simp only [Function.mem_support, Function.comp_apply, hsl]
    exact hts
  exact ⟨⟨slot, hmem⟩, hsl⟩


theorem relation_of_partitionFacts (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0)
    (hp : Summable fun ts => parafSummand region a h0 (v + du) (5/8) hexChi ts)
    (hq : Summable fun ts => parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi ts)
    (hr : Summable fun ts => parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi ts)
    (htinj : ∀ T1 T2 : E.triplets, E.tripBase T1 = E.tripBase T2 → T1 = T2)
    (hqinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLq P1 = E.pairBase P2 ++ E.pairLq P2 → P1 = P2)
    (hrinj : ∀ P1 P2 : E.pairs,
        E.pairBase P1 ++ E.pairLr P1 = E.pairBase P2 ++ E.pairLr P2 → P1 = P2)
    (hqcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLq P ≠ E.tripBase T ++ [-1])
    (hrcross : ∀ (P : E.pairs) (T : E.triplets),
        E.pairBase P ++ E.pairLr P ≠ E.tripBase T ++ [1])
    (covp : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + du) → ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covq : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts)
    (covr : ∀ ts ∈ Function.support (combinedSummand region a h0 v du),
        (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) →
        ∃ slot : SlotType E, E.slotTurns slot = ts) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 :=
  HexVertexEnumeration.relation_of_bijection E hdu hp hq hr
    (hinj_general E hdu htinj hqinj hrinj hqcross hrcross)
    (hsub_of_coverage E covp covq covr)


theorem parafSummand_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) (ts : List ℤ) :
    parafSummand (fun _ => False) a h0 z σ x ts = 0 := by
  unfold parafSummand
  rw [if_neg]
  rintro ⟨_, hstay, _⟩
  have hne : (ofTurns a h0 ts).mids ≠ [] := by
    intro h
    have := HexWalk.length_mids (ofTurns a h0 ts)
    rw [h] at this; simp at this
  obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil _ hne
  exact hstay m hm


theorem parafObservable_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    parafObservable (fun _ => False) a h0 z σ x = 0 := by
  unfold parafObservable
  rw [show (fun ts => parafSummand (fun _ => False) a h0 z σ x ts) = (fun _ => (0 : ℂ)) from
    funext fun ts => parafSummand_emptyRegion a h0 z σ x ts]
  exact tsum_zero


theorem combinedSummand_emptyRegion (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts : List ℤ) :
    combinedSummand (fun _ => False) a h0 v du ts = 0 := by
  unfold combinedSummand
  rw [parafSummand_emptyRegion, parafSummand_emptyRegion, parafSummand_emptyRegion]
  ring


theorem summable_emptyRegion (a : ℂ) (h0 : ℤ) (z : ℂ) (σ x : ℝ) :
    Summable fun ts => parafSummand (fun _ => False) a h0 z σ x ts := by
  rw [show (fun ts => parafSummand (fun _ => False) a h0 z σ x ts) = (fun _ => (0 : ℂ)) from
    funext fun ts => parafSummand_emptyRegion a h0 z σ x ts]
  exact summable_zero


end StatMech.Universality

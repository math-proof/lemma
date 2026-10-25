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
import Def.StatisticalMechanics.Code.Universality.HexVertexBijection


namespace StatMech.Universality

open Complex

open Function

open HexWalk


variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem slot_endsAt_label (E : HexVertexEnumeration region a h0 v du)
    (slot : (E.pairs × Bool) ⊕ (E.triplets × Fin 3)) :
    (ofTurns a h0 (E.slotTurns slot)).EndsAt (labelMid v du (slotLabel slot)) := by
  rcases slot with (⟨P, b⟩ | ⟨T, i⟩)
  · cases b with
    | false => exact (E.pairQ_valid P P.2).2.2
    | true  => exact (E.pairR_valid P P.2).2.2
  · match i with
    | ⟨0, _⟩ => exact (E.tripP_valid T T.2).2.2
    | ⟨1, _⟩ => exact (E.tripQ_valid T T.2).2.2
    | ⟨2, _⟩ => exact (E.tripR_valid T T.2).2.2


theorem labelMid_injective (hdu : du ≠ 0) : Function.Injective (labelMid v du) := by
  intro i j h
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨2, _⟩, ⟨2, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ => exact absurd h (hexMid_p_ne_q hdu)
  | ⟨0, _⟩, ⟨2, _⟩ => exact absurd h (hexMid_p_ne_r hdu)
  | ⟨1, _⟩, ⟨0, _⟩ => exact absurd h (fun hh => hexMid_p_ne_q hdu hh.symm)
  | ⟨1, _⟩, ⟨2, _⟩ => exact absurd h (hexMid_q_ne_r hdu)
  | ⟨2, _⟩, ⟨0, _⟩ => exact absurd h (fun hh => hexMid_p_ne_r hdu hh.symm)
  | ⟨2, _⟩, ⟨1, _⟩ => exact absurd h (fun hh => hexMid_q_ne_r hdu hh.symm)


theorem slotLabel_eq_of_slotTurns_eq (E : HexVertexEnumeration region a h0 v du)
    (hdu : du ≠ 0) (s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3))
    (h : E.slotTurns s1 = E.slotTurns s2) : slotLabel s1 = slotLabel s2 := by
  apply labelMid_injective hdu
  have h1 := slot_endsAt_label E s1
  have h2 := slot_endsAt_label E s2
  unfold HexWalk.EndsAt at h1 h2
  rw [← h1, ← h2, h]


theorem support_endsAt_threeMid (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand region a h0 v du)) :
    (ofTurns a h0 ts).EndsAt (v + du) ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega * du)
      ∨ (ofTurns a h0 ts).EndsAt (v + hexOmega ^ 2 * du) := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨hnp, hnq, hnr⟩ := hcon
  apply h
  show combinedSummand region a h0 v du ts = 0
  unfold combinedSummand
  rw [parafSummand_eq_zero_of_not_endsAt region a h0 (v + du) _ _ ts hnp,
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega * du) _ _ ts hnq,
      parafSummand_eq_zero_of_not_endsAt region a h0 (v + hexOmega ^ 2 * du) _ _ ts hnr]
  ring


theorem support_isLegalSAW (ts : List ℤ)
    (h : ts ∈ Function.support (combinedSummand region a h0 v du))
    (hp : (ofTurns a h0 ts).EndsAt (v + du)) (hdu : du ≠ 0) :
    (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region := by
  have hcs : combinedSummand region a h0 v du ts
      = ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts :=
    combinedSummand_at_p hdu hp
  have hne : parafSummand region a h0 (v + du) (5/8) hexChi ts ≠ 0 := by
    intro hz
    apply h
    show combinedSummand region a h0 v du ts = 0
    rw [hcs, hz, mul_zero]
  unfold parafSummand at hne
  by_contra hcon
  rw [not_and_or] at hcon
  apply hne
  rw [if_neg]
  rintro ⟨h1, h2, _⟩
  rcases hcon with h1' | h2'
  · exact h1' h1
  · exact h2' h2


theorem hinj_of_perLabel (E : HexVertexEnumeration region a h0 v du) (hdu : du ≠ 0)
    (hlabel : ∀ s1 s2 : (E.pairs × Bool) ⊕ (E.triplets × Fin 3),
        slotLabel s1 = slotLabel s2 → E.slotTurns s1 = E.slotTurns s2 → s1 = s2) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  apply Subtype.ext
  exact hlabel x y (slotLabel_eq_of_slotTurns_eq E hdu x y h) h


theorem hinj_of_injective (E : HexVertexEnumeration region a h0 v du)
    (hsti : Function.Injective E.slotTurns) :
    Function.Injective
      fun x : Function.support (combinedSummand region a h0 v du ∘ E.slotTurns) =>
        E.slotTurns x.1 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  simp only at h
  exact Subtype.ext (hsti h)


end StatMech.Universality

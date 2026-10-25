import Mathlib
import Class.Analysis.Misc.erdos_707


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

lemma h1 : 1 ∈ B := by
  convert (embed ⟨ 1, by grind ⟩).property
  simp [h_embed]

lemma h2 : 2 ∈ B := by
  convert (embed ⟨ 2, by grind ⟩).property
  simp [h_embed]

lemma h4 : 4 ∈ B := by
  convert (embed ⟨ 4, by grind ⟩).property
  simp [h_embed]

lemma h8 : 8 ∈ B := by
  convert (embed ⟨ 8, by grind ⟩).property
  simp [h_embed]

lemma h2_ne_1: (2: ZMod N) ≠ (1: ZMod N) := by
  have : (embed ⟨ 2, by grind ⟩).val ≠ (embed ⟨ 1, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

lemma h4_ne_1: (4: ZMod N) ≠ (1: ZMod N) := by
  have : (embed ⟨ 4, by grind ⟩).val ≠ (embed ⟨ 1, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

lemma h4_ne_8: (4: ZMod N) ≠ (8: ZMod N) := by
  have : (embed ⟨ 4, by grind ⟩).val ≠ (embed ⟨ 8, by grind ⟩).val := by
    rw [Subtype.coe_ne_coe]
    by_contra!
    replace := h_inj this
    grind
  convert this <;> simp [h_embed]

lemma hodd : Odd N := by
  rw [hN]
  grind

lemma card_B : B.card = p + 1 := by
  have hnon : NeZero N := by rw [neZero_iff, hN]; grind
  have := hdiff.card
  have h1 := Finset.card_le_card_of_injective h_inj
  simp at h1
  replace : B.card * B.card = p^2 + p + B.card := by grind [hN]
  replace : (B.card:ℤ) * B.card = p^2 + p + B.card := by grind
  replace : ((B.card:ℤ) - (p + 1)) * (B.card + p) = 0 := by grind
  rw [mul_eq_zero] at this
  grind

lemma odd_P : Odd p := by
  apply Nat.Prime.odd_of_ne_two hp
  by_contra!
  replace := this ▸ card_B
  have h1 := Finset.card_le_card_of_injective h_inj
  simp at h1
  grind

lemma heven : Even B.card := by
  rw [card_B]
  grind [odd_P]

lemma mul_two_inj {x y: ZMod N} (h: 2 * x = 2 * y) : x = y := by
  apply IsUnit.mul_left_cancel _ h
  convert (ZMod.isUnit_prime_iff_not_dvd (n := N) Nat.prime_two).mpr _
  exact Odd.not_two_dvd_nat hodd

lemma diff_uniq {a b c d:B} (ha: a ≠ b) (hsub: a.val-b.val = c.val-d.val) : a=c ∧ b=d := by
  have := hdiff (a-b) (by grind)
  replace : (⟨ a, b ⟩: B × B) = ⟨ c, d ⟩ := by apply this.unique <;> grind
  grind

end Mainstep

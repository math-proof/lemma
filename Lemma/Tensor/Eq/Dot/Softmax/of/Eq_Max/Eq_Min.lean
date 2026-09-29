import sympy.functions.elementary.band_window
import sympy.Basic


@[main]
private lemma band_part_mask.dilated
  {n l u d d_z : ℕ}
  {β : Fin n → ℕ}
  {A : Fin n → Fin n → ℝ}
  {V : Fin n → Fin d_z → ℝ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d)) :
-- imply
  ∀ (i : Fin n) (t : Fin d_z), ∑ j, maskedSoftmax (A i) (fun j : Fin n => if ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0) then 1 else 0) j * V j t =
    ∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp (A i ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp (A i ⟨β i + m' * d, by have := Band.win_lt h_d m'.2; omega⟩)) * V ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ t := by
-- proof
  intro i t
  obtain ⟨hb1, hb2, hb3⟩ := Band.beta_props h_d h_dl (h_β i)
  exact Band.softmax_dilated i l u d (β i) h_d hb1 hb2 hb3 _ (fun j => V j t)


@[main]
private lemma band_part_mask.dilated.bert
  {n l u d d_z : ℕ}
  {β : Fin n → ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d)) :
-- imply
  ∀ (i : Fin n) (t : Fin d_z), ∑ j, maskedSoftmax (fun j => (∑ s, Q i s * K j s) / √d_z) (fun j : Fin n => if ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0) then 1 else 0) j * V j t =
    ∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ s, Q i s * K ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ s) / √d_z) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ s, Q i s * K ⟨β i + m' * d, by have := Band.win_lt h_d m'.2; omega⟩ s) / √d_z)) * V ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ t := by
-- proof
  intro i t
  obtain ⟨hb1, hb2, hb3⟩ := Band.beta_props h_d h_dl (h_β i)
  exact Band.softmax_dilated i l u d (β i) h_d hb1 hb2 hb3 _ (fun j => V j t)


-- created on 2026-09-27

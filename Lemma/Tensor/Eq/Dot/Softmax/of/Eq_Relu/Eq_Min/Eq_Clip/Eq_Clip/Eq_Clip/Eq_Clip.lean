import sympy.functions.elementary.band_window
import sympy.Basic


@[main]
private lemma position_representation.relative.band_part_mask.indexed
  {n d_z : ℕ}
  {l u : ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {K'' V'' : Fin n → ℕ → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t)
  (h₂ : ∀ (i : Fin n) (j : ℕ) t, K'' i j t = wK (c + max (-c) (min (r ⟨min (n - 1) (j + (i.val + 1 - l)), by have := i.2; omega⟩ - r i) c)) t)
  (h₃ : ∀ (i : Fin n) (j : ℕ) t, V'' i j t = wV (c + max (-c) (min (r ⟨min (n - 1) (j + (i.val + 1 - l)), by have := i.2; omega⟩ - r i) c)) t) :
-- imply
  ∀ (i : Fin n) (s : Fin d_z), ∑ j, maskedSoftmax (fun j => ((∑ t, Q i t * (K j t + K' i j t)) / √d_z)) (fun j : Fin n => if ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j * (V j s + V' i j s) =
    ∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp ((∑ t, Q i t * (K ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ t + K'' i j' t)) / √d_z) / (∑ k' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp ((∑ t, Q i t * (K ⟨i.val + 1 - l + k', by have := k'.2; omega⟩ t + K'' i k' t)) / √d_z)) * (V ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ s + V'' i j' s) := by
-- proof
  intro i s
  rw [Band.softmax_window i l u]
  have e : ∀ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), ((⟨min (n - 1) (j'.val + (i.val + 1 - l)), by have := i.2; omega⟩ : Fin n)) = ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ :=
    fun j' => Fin.ext (by have := j'.2; simp only; omega)
  simp only [h₀, h₁, h₂, h₃, e]


-- created on 2026-09-27

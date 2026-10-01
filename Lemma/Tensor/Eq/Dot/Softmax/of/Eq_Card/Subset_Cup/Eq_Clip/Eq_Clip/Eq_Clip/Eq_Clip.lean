import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma position_representation.relative.gather
  {n d_z : ℕ}
  {m : ℕ}
  {dm : Fin m → Fin n}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t) :
-- imply
  ∀ (i : Fin n) (s : Fin d_z), ∑ j, maskedSoftmax (fun j => ((∑ t, Q i t * (K j t + K' i j t)) / √d_z)) (fun j => if j ∈ Finset.univ.image dm then 1 else 0) j * (V j s + V' i j s) =
    ∑ j, Real.exp ((∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K (dm k) t + wK (c + max (-c) (min (((dm k).val : ℤ) - i.val) c)) t)) / √d_z)) * (V (dm j) s + wV (c + max (-c) (min (((dm j).val : ℤ) - i.val) c)) s) := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hd : Set.InjOn dm (Finset.univ : Finset (Fin m)) := by
    rw [← Finset.card_image_iff, h, Finset.card_univ, Fintype.card_fin]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin m)), ∀ y ∈ (Finset.univ : Finset (Fin m)), dm x = dm y → x = y :=
    fun x hx y hy hxy => hd (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  intro i s
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, h₀, h₁]
  rw [Finset.sum_image hinj, Finset.sum_image hinj]


@[main]
private lemma position_representation.relative.gather.indexed
  {n d_z : ℕ}
  {m : ℕ}
  {dm : Fin m → Fin n}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t) :
-- imply
  ∀ (i : Fin n) (s : Fin d_z), ∑ j, maskedSoftmax (fun j => ((∑ t, Q i t * (K j t + K' i j t)) / √d_z)) (fun j => if j ∈ Finset.univ.image dm then 1 else 0) j * (V j s + V' i j s) =
    ∑ j, Real.exp ((∑ t, Q i t * (K (dm j) t + wK (c + max (-c) (min (r (dm j) - r i) c)) t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K (dm k) t + wK (c + max (-c) (min (r (dm k) - r i) c)) t)) / √d_z)) * (V (dm j) s + wV (c + max (-c) (min (r (dm j) - r i) c)) s) := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hd : Set.InjOn dm (Finset.univ : Finset (Fin m)) := by
    rw [← Finset.card_image_iff, h, Finset.card_univ, Fintype.card_fin]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin m)), ∀ y ∈ (Finset.univ : Finset (Fin m)), dm x = dm y → x = y :=
    fun x hx y hy hxy => hd (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  intro i s
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, h₀, h₁]
  rw [Finset.sum_image hinj, Finset.sum_image hinj]


-- created on 2026-09-27

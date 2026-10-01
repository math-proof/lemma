import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma gather
  {n m d_z : ℕ}
  {d : Fin m → Fin n}
  {A : Fin n → Fin n → ℝ}
  {V : Fin n → Fin d_z → ℝ}
-- given
  (h₀ : (Finset.univ.image d).card = m) :
-- imply
  (fun i l => ∑ j, maskedSoftmax (A i) (fun j => if j ∈ Finset.univ.image d then 1 else 0) j * V j l) =
    fun i l => ∑ j, Real.exp (A i (d j)) / (∑ k, Real.exp (A i (d k))) * V (d j) l := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hd : Set.InjOn d (Finset.univ : Finset (Fin m)) := by
    rw [← Finset.card_image_iff, h₀, Finset.card_univ, Fintype.card_fin]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin m)), ∀ y ∈ (Finset.univ : Finset (Fin m)), d x = d y → x = y :=
    fun x hx y hy hxy => hd (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  funext i l
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_image hinj, Finset.sum_image hinj]


@[main]
private lemma position_representation.relative.gather
  {n m d_z : ℕ}
  {d : Fin m → Fin n}
  {Q K K' V V' : Fin n → Fin d_z → ℝ}
-- given
  (h₀ : (Finset.univ.image d).card = m) :
-- imply
  (fun i l => ∑ j, maskedSoftmax (fun j => (∑ t, Q i t * (K j t + K' j t)) / √d_z) (fun j => if j ∈ Finset.univ.image d then 1 else 0) j * (V j l + V' j l)) =
    fun i l => ∑ j, Real.exp ((∑ t, Q i t * (K (d j) t + K' (d j) t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K (d k) t + K' (d k) t)) / √d_z)) * (V (d j) l + V' (d j) l) := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  have hd : Set.InjOn d (Finset.univ : Finset (Fin m)) := by
    rw [← Finset.card_image_iff, h₀, Finset.card_univ, Fintype.card_fin]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin m)), ∀ y ∈ (Finset.univ : Finset (Fin m)), d x = d y → x = y :=
    fun x hx y hy hxy => hd (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  funext i l
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [Finset.sum_image hinj, Finset.sum_image hinj]


-- created on 2022-01-09

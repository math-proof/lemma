import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private def prodTwist {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) : ℕ → Matrix (Fin d) (Fin d) S :=
  fun n => Nat.rec (1 : Matrix (Fin d) (Fin d) S) (fun _ ih => D * ih.map σ) n

private lemma prodTwist_zero {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) : prodTwist σ D 0 = 1 := rfl

private lemma prodTwist_succ {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) (m : ℕ) : prodTwist σ D (m + 1) = D * (prodTwist σ D m).map σ := rfl

private lemma map_iterate_mul {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (k : ℕ) (M N : Matrix (Fin d) (Fin d) S) : (M * N).map (Nat.iterate σ k) = M.map (Nat.iterate σ k) * N.map (Nat.iterate σ k) := by
  induction k generalizing M N
  · simp
  ·
    rename_i k ih
    rw [Function.iterate_succ', ← Matrix.map_map, ← Matrix.map_map, ← Matrix.map_map, ih, Matrix.map_mul]

private lemma prodTwist_add {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) (m : ℕ) : ∀ k, prodTwist σ D (m + k) = prodTwist σ D k * (prodTwist σ D m).map (Nat.iterate σ k) := by
  intro k
  induction k
  · simp [prodTwist_zero]
  ·
    rename_i k ih
    rw [← add_assoc, prodTwist_succ, ih, Matrix.map_mul, Matrix.map_map, prodTwist_succ, mul_assoc, ← Function.iterate_succ']

private lemma prodTwist_map {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} {T : Type v} [CommRing T] (τ : T →+* T) (f : S →+* T) (hf : ∀ s, f (σ s) = τ (f s)) (D : Matrix (Fin d) (Fin d) S) : ∀ m, (prodTwist σ D m).map f = prodTwist τ (D.map f) m := by
  intro m
  induction m
  · simp [prodTwist_zero]
  ·
    rename_i m ih
    rw [prodTwist_succ, prodTwist_succ, Matrix.map_mul, Matrix.map_map]
    congr 1
    rw [← ih, Matrix.map_map]
    congr 1
    funext s
    exact hf s

private lemma prodTwist_apply_eq_zero {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j = 0) : ∀ (m : ℕ) (i j : Fin d), (j : ℕ) < i + m → prodTwist σ D m i j = 0 := by
  intro m
  induction m
  ·
    intro i j hij
    rw [prodTwist_zero, Matrix.one_apply, ite_eq_right]
    rintro rfl
    omega
  ·
    rename_i m ih
    intro i j hij
    rw [prodTwist_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    if hl : l ≤ i then
      rw [hD i l hl, zero_mul]
    else
      have hlt : (j : ℕ) < l + m := by
        have := Fin.lt_def.mp (not_le.mp hl)
        omega
      rw [Matrix.map_apply, ih l j hlt, map_zero, mul_zero]

private lemma prodTwist_eq_zero {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j = 0) : prodTwist σ D d = 0 := by
  ext i j
  refine prodTwist_apply_eq_zero σ D hD d i j (by omega)

private lemma map_mem_pow {S : Type u} [CommRing S] (σ : S →+* S) (𝔫 : Ideal S) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫) (t : ℕ) : ∀ s ∈ 𝔫 ^ t, σ s ∈ 𝔫 ^ t := by
  intro s hs
  induction t generalizing s
  ·
    rw [pow_zero, Ideal.one_eq_top]
    refine Submodule.mem_top
  ·
    rename_i t ih
    rw [pow_succ] at hs ⊢
    refine Submodule.mul_induction_on hs (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    ·
      rw [map_mul]
      refine Ideal.mul_mem_mul (ih a ha) (hσ b hb)
    ·
      rw [map_add]
      refine Ideal.add_mem _ ha hb

private lemma iterate_map_mem_pow {S : Type u} [CommRing S] (σ : S →+* S) (𝔫 : Ideal S) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫) (t : ℕ) : ∀ (k : ℕ) (s : S), s ∈ 𝔫 ^ t → Nat.iterate σ k s ∈ 𝔫 ^ t := by
  intro k
  induction k
  ·
    intro s hs
    exact hs
  ·
    rename_i k ih
    intro s hs
    rw [Function.iterate_succ_apply']
    refine map_mem_pow σ 𝔫 hσ t _ (ih s hs)

private lemma prodTwist_mul_eq_zero {S : Type u} [CommRing S] (σ : S →+* S) {d : ℕ} (𝔫 : Ideal S) (K : ℕ) (hK : 𝔫 ^ K = 0) (hσ : ∀ s ∈ 𝔫, σ s ∈ 𝔫) (τ : S ⧸ 𝔫 →+* S ⧸ 𝔫) (hτ : ∀ s, Ideal.Quotient.mk 𝔫 (σ s) = τ (Ideal.Quotient.mk 𝔫 s)) (D : Matrix (Fin d) (Fin d) S) (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫) : prodTwist σ D (K * d) = 0 := by
  have hd : ∀ i j, prodTwist σ D d i j ∈ 𝔫 := by
    intro i j
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Matrix.map_apply (f := Ideal.Quotient.mk 𝔫), prodTwist_map σ τ (Ideal.Quotient.mk 𝔫) hτ D d, prodTwist_eq_zero τ (D.map (Ideal.Quotient.mk 𝔫)) (fun i j hij => (Ideal.Quotient.eq_zero_iff_mem).2 (hD i j hij))]
    rfl
  have ht : ∀ (t : ℕ) (i j), prodTwist σ D (t * d) i j ∈ 𝔫 ^ t := by
    intro t
    induction t
    ·
      intro i j
      rw [pow_zero, Ideal.one_eq_top]
      refine Submodule.mem_top
    ·
      rename_i t ih
      intro i j
      rw [show (t + 1) * d = d + t * d by ring, prodTwist_add, Matrix.mul_apply, pow_succ]
      refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_mul (ih i l) ?_
      rw [Matrix.map_apply]
      exact (pow_one 𝔫) ▸ iterate_map_mem_pow σ 𝔫 hσ 1 (t * d) _ ((pow_one 𝔫).symm ▸ hd l j)
  ext i j
  have h := ht K i j
  rwa [hK, Submodule.zero_eq_bot, Ideal.mem_bot] at h

/--
[Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_existsUnique_add_mulVec_pow_eq_of_forall_mem_of_isNilpotent.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S]
  (p : ℕ) [Fact p.Prime] [CharP S p]
  {d : ℕ}
  (𝔫 : Ideal S)
  (D : Matrix (Fin d) (Fin d) S)
  (b : Fin d → S)
  -- given
  (h𝔫 : IsNilpotent 𝔫)
  (hD : ∀ i j : Fin d, j ≤ i → D i j ∈ 𝔫) :
  -- imply
  ∃! y : Fin d → S, y + D.mulVec (fun j => y j ^ p) = b := by
  -- proof
  classical
  have hpp : p.Prime := Fact.out
  let _ : ExpChar S p := ExpChar.prime hpp
  obtain ⟨K, hK⟩ := h𝔫
  let σ : S →+* S := frobenius S p
  have hσ : ∀ s, σ s = s ^ p := fun s => frobenius_def p s
  have hσ𝔫 : ∀ s ∈ 𝔫, σ s ∈ 𝔫 := fun s hs => by
    rw [hσ]
    refine Ideal.pow_mem_of_mem 𝔫 hs p hpp.pos
  have hle : 𝔫 ≤ Ideal.comap σ 𝔫 := fun s hs => hσ𝔫 s hs
  let τ : S ⧸ 𝔫 →+* S ⧸ 𝔫 := Ideal.quotientMap 𝔫 σ hle
  have hτ : ∀ s, Ideal.Quotient.mk 𝔫 (σ s) = τ (Ideal.Quotient.mk 𝔫 s) := fun s => (Ideal.quotientMap_mk (f := σ) (H := hle)).symm
  set M := K * d
  have hPi : prodTwist σ D M = 0 := prodTwist_mul_eq_zero σ 𝔫 K hK hσ𝔫 τ hτ D hD
  have hvec : ∀ y : Fin d → S, (fun j => y j ^ p) = ⇑σ ∘ y := fun y => by
    funext j
    exact (hσ (y j)).symm
  let f : ℕ → Fin d → S := fun m => (-1 : S) ^ m • (prodTwist σ D m).mulVec (Nat.iterate σ m ∘ b)
  have hf : ∀ m, f m = (-1 : S) ^ m • (prodTwist σ D m).mulVec (Nat.iterate σ m ∘ b) := fun _ => rfl
  have hf0 : f 0 = b := by
    rw [hf, pow_zero, one_smul, prodTwist_zero, Matrix.one_mulVec, Function.iterate_zero, Function.id_comp]
  have hfM : f M = 0 := by rw [hf, hPi, Matrix.zero_mulVec, smul_zero]
  have htwist : ∀ (m : ℕ) (w : Fin d → S), ⇑σ ∘ ((-1 : S) ^ m • (prodTwist σ D m).mulVec (Nat.iterate σ m ∘ w)) = (-1 : S) ^ m • (((prodTwist σ D m).map σ).mulVec (Nat.iterate σ (m + 1) ∘ w)) := by
    intro m w
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, map_neg, map_one]
    congr 1
    rw [RingHom.map_mulVec, Function.iterate_succ']
    rfl
  have hstep : ∀ m, D.mulVec (⇑σ ∘ f m) = -f (m + 1) := by
    intro m
    rw [hf, hf]
    have h1 := htwist m b
    rw [h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← prodTwist_succ, pow_succ, mul_neg_one, neg_smul, neg_neg]
  set y₀ : Fin d → S := ∑ m ∈ Finset.range M, f m with hy₀def
  have hy₀ : y₀ + D.mulVec (fun j => y₀ j ^ p) = b := by
    rw [hvec]
    have hsum : ⇑σ ∘ y₀ = ∑ m ∈ Finset.range M, ⇑σ ∘ f m := by
      funext j
      simp only [hy₀def, Function.comp_apply, Finset.sum_apply, map_sum]
    rw [hsum, ← Matrix.mulVecLin_apply, map_sum]
    simp only [Matrix.mulVecLin_apply, hstep, Finset.sum_neg_distrib]
    rw [hy₀def, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    have htel := Finset.sum_range_sub f M
    rw [hfM, hf0, zero_sub] at htel
    have : ∑ m ∈ Finset.range M, (f m - f (m + 1)) = -∑ m ∈ Finset.range M, (f (m + 1) - f m) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => (neg_sub _ _).symm
    rw [this, htel, neg_neg]
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  have hy' : y + D.mulVec (⇑σ ∘ y) = b := by
    have h := hy
    simp only at h
    rwa [hvec] at h
  have hy₀' : y₀ + D.mulVec (⇑σ ∘ y₀) = b := by
    rwa [hvec] at hy₀
  set δ := y - y₀ with hδdef
  have hσδ : ⇑σ ∘ δ = ⇑σ ∘ y - ⇑σ ∘ y₀ := by
    funext j
    simp only [hδdef, Function.comp_apply, Pi.sub_apply, map_sub]
  have hδ : δ = -(D.mulVec (⇑σ ∘ δ)) := by
    rw [hσδ, Matrix.mulVec_sub, hδdef]
    have h : (y + D.mulVec (⇑σ ∘ y)) - (y₀ + D.mulVec (⇑σ ∘ y₀)) = 0 := by
      rw [hy', hy₀', sub_self]
    rw [← sub_eq_zero, ← h]
    abel
  have hiter : ∀ m, δ = (-1 : S) ^ m • (prodTwist σ D m).mulVec (Nat.iterate σ m ∘ δ) := by
    intro m
    induction m
    · rw [pow_zero, one_smul, prodTwist_zero, Matrix.one_mulVec, Function.iterate_zero, Function.id_comp]
    ·
      rename_i m ih
      conv_lhs => rw [hδ, ih]
      rw [htwist, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← prodTwist_succ, pow_succ, mul_neg_one, neg_smul]
  have hδ0 : δ = 0 := by
    rw [hiter M, hPi, Matrix.zero_mulVec, smul_zero]
  rwa [hδdef, sub_eq_zero] at hδ0


-- created on 2026-10-20

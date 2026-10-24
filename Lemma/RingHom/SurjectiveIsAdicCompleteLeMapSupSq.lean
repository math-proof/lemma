import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_surjective_of_isAdicComplete_of_le_map_sup_sq.lean)
-/
@[path]
private lemma main
  {P R : Type u} [CommRing P] [CommRing R] (J : Ideal P) [IsAdicComplete J P] (I : Ideal R) [IsHausdorff I R] (φ : P →+* R)
  -- given
  (hJ : Ideal.map φ J ≤ I)
  (h0 : ∀ r : R, ∃ p : P, r - φ p ∈ I)
  (h1 : I ≤ Ideal.map φ J ⊔ I ^ 2) :
  -- imply
  Function.Surjective φ := by
  -- proof
  classical
  have hJn : ∀ n : ℕ, Ideal.map φ (J ^ n) ≤ I ^ n := by
    intro n
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono hJ n
  have hA : ∀ (n : ℕ) (y : R), y ∈ Ideal.map φ (J ^ n) → ∃ j ∈ J ^ n, y - φ j ∈ I ^ (n + 1) := by
    intro n y hy
    replace hy : y ∈ Submodule.span R (⇑φ '' ↑(J ^ n)) := hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    ·
      intro x hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨j, hj, by simp⟩
    · exact ⟨0, Submodule.zero_mem _, by simp⟩
    ·
      intro x y _ _ hx hy
      obtain ⟨j₁, hj₁, h₁⟩ := hx
      obtain ⟨j₂, hj₂, h₂⟩ := hy
      refine ⟨j₁ + j₂, add_mem hj₁ hj₂, ?_⟩
      have : x + y - φ (j₁ + j₂) = (x - φ j₁) + (y - φ j₂) := by
        rw [map_add]
        ring
      rw [this]
      apply add_mem h₁ h₂
    ·
      intro a x _ hx
      obtain ⟨j, hj, h⟩ := hx
      obtain ⟨p, hp⟩ := h0 a
      refine ⟨p * j, Ideal.mul_mem_left _ _ hj, ?_⟩
      have : a • x - φ (p * j) = a * (x - φ j) + (a - φ p) * φ j := by
        rw [smul_eq_mul, map_mul]
        ring
      rw [this]
      refine add_mem (Ideal.mul_mem_left _ _ h) ?_
      rw [pow_succ']
      apply Ideal.mul_mem_mul hp (hJn n (Ideal.mem_map_of_mem φ hj))
  have hA1 : ∀ a ∈ I, ∃ j ∈ J, a - φ j ∈ I ^ 2 := by
    intro a ha
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h1 ha)
    obtain ⟨j, hj, h⟩ := hA 1 y (by simp; apply hy)
    simp at hj
    simp at h
    refine ⟨j, hj, ?_⟩
    have : y + z - φ j = (y - φ j) + z := by ring
    rw [this]
    apply add_mem h hz
  have hB : ∀ (n : ℕ) (x : R), x ∈ I ^ n → ∃ j ∈ J ^ n, x - φ j ∈ I ^ (n + 1) := by
    intro n
    induction n
    ·
      intro x _
      obtain ⟨p, hp⟩ := h0 x
      refine ⟨p, by simp, ?_⟩
      simp
      apply hp
    ·
      rename_i n ih
      intro x hx
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on' ?_ ?_ hx
      ·
        intro a ha x hx
        obtain ⟨j₁, hj₁, h₁⟩ := hA1 a ha
        obtain ⟨j, hj, h⟩ := ih x hx
        refine ⟨j₁ * j, ?_, ?_⟩
        ·
          rw [pow_succ']
          apply Ideal.mul_mem_mul hj₁ hj
        have : a * x - φ (j₁ * j) = a * (x - φ j) + (a - φ j₁) * φ j := by
          rw [map_mul]
          ring
        rw [this]
        refine add_mem ?_ ?_
        ·
          rw [pow_succ']
          apply Ideal.mul_mem_mul ha h
        ·
          rw [show n + 1 + 1 = 2 + n by ring, pow_add]
          apply Ideal.mul_mem_mul h₁ (hJn n (Ideal.mem_map_of_mem φ hj))
      ·
        intro x _ y _ hx hy
        obtain ⟨j₁, hj₁, h₁⟩ := hx
        obtain ⟨j₂, hj₂, h₂⟩ := hy
        refine ⟨j₁ + j₂, add_mem hj₁ hj₂, ?_⟩
        have : x + y - φ (j₁ + j₂) = (x - φ j₁) + (y - φ j₂) := by
          rw [map_add]
          ring
        rw [this]
        apply add_mem h₁ h₂
  have eP : ∀ n : ℕ, (J ^ n • ⊤ : Submodule P P) = J ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  have eR : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  intro r
  have hnext : ∀ (n : ℕ) (p : P), r - φ p ∈ I ^ (n + 1) → ∃ p' : P, p' - p ∈ J ^ (n + 1) ∧ r - φ p' ∈ I ^ (n + 1 + 1) := by
    intro n p hp
    obtain ⟨j, hj, h⟩ := hB (n + 1) _ hp
    refine ⟨p + j, by simp; apply hj, ?_⟩
    have : r - φ (p + j) = r - φ p - φ j := by
      rw [map_add]
      ring
    rwa [this]
  choose nxt hnxt using hnext
  obtain ⟨p₀, hp₀⟩ := h0 r
  let q : (n : ℕ) → Subtype fun p : P => r - φ p ∈ I ^ (n + 1) := fun n => Nat.rec (motive := fun n => Subtype fun p : P => r - φ p ∈ I ^ (n + 1)) ⟨p₀, by simp; apply hp₀⟩ (fun n qn => ⟨nxt n qn.1 qn.2, (hnxt n qn.1 qn.2).2⟩) n
  have hq_succ : ∀ n, (q (n + 1)).1 - (q n).1 ∈ J ^ (n + 1) := fun n => (hnxt n (q n).1 (q n).2).1
  let f : ℕ → P := fun n => (q n).1
  have hf_succ : ∀ n, f n ≡ f (n + 1) [SMOD (J ^ (n + 1) • ⊤ : Submodule P P)] := by
    intro n
    rw [SModEq.sub_mem, eP, ← neg_mem_iff, neg_sub]
    apply hq_succ n
  have hf : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD (J ^ m • ⊤ : Submodule P P)] := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    induction k
    · apply SModEq.rfl
    ·
      rename_i k ih
      refine (ih (Nat.le_add_right m k)).trans ?_
      rw [← add_assoc]
      apply (hf_succ (m + k)).mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))
  obtain ⟨L, hL⟩ := (IsAdicComplete.toIsPrecomplete (I := J) (M := P)).prec hf
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine (‹IsHausdorff I R›).haus _ fun n => ?_
  rw [SModEq.zero, eR]
  have h₁ : f n - L ∈ J ^ n := by
    rw [← eP, ← SModEq.sub_mem]
    apply hL n
  have h₂ : r - φ (f n) ∈ I ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) (q n).2
  have : φ L - r = -(φ (f n - L) + (r - φ (f n))) := by
    rw [map_sub]
    ring
  rw [this]
  apply neg_mem (add_mem (hJn n (Ideal.mem_map_of_mem φ h₁)) h₂)


-- created on 2026-10-20

import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def pt (a ℓ : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  a + i * (ℓ / N)

private noncomputable def walk (a b l : ℕ) : ℕ :=
  if a ≤ b then min (a + l) b else max (a - l) b

private noncomputable def len (a b : ℕ) : ℕ :=
  (a - b) + (b - a)

private lemma step_nonneg
  {ℓ : ℝ}
  (hℓ : 0 ≤ ℓ)
  (N : ℕ) :
  -- imply
  0 ≤ ℓ / N :=
  div_nonneg hℓ (Nat.cast_nonneg N)

private lemma step_le
  {ℓ δ : ℝ}
  (hδ : 0 < δ) :
  -- imply
  ℓ / (⌈2 * ℓ / δ⌉₊ : ℕ) ≤ δ / 2 := by
  -- proof
  obtain hN | hN := Nat.eq_zero_or_pos ⌈2 * ℓ / δ⌉₊
  ·
    rw [hN, Nat.cast_zero, div_zero]
    linarith
  ·
    rw [div_le_iff₀ (by exact_mod_cast hN)]
    have h := Nat.le_ceil (2 * ℓ / δ)
    rw [div_le_iff₀ hδ] at h
    calc
      _ = (2 * ℓ) / 2 := by ring
      _ ≤ (⌈2 * ℓ / δ⌉₊ * δ) / 2 := by gcongr
      _ = δ / 2 * ⌈2 * ℓ / δ⌉₊ := by ring

private lemma ceil_eq_zero_imp
  {ℓ δ : ℝ}
  (hℓ : 0 ≤ ℓ)
  (hδ : 0 < δ)
  (h : ⌈2 * ℓ / δ⌉₊ = 0) :
  -- imply
  ℓ = 0 := by
  -- proof
  rw [Nat.ceil_eq_zero] at h
  have h2 : 2 * ℓ / δ * δ ≤ 0 * δ := mul_le_mul_of_nonneg_right h hδ.le
  rw [div_mul_cancel₀ _ hδ.ne', zero_mul] at h2
  linarith

private lemma pt_sub (a ℓ : ℝ) (N p q : ℕ) :
  -- imply
  pt a ℓ N p - pt a ℓ N q = ((p : ℝ) - q) * (ℓ / N) := by
  -- proof
  unfold pt
  ring

private lemma pt_mem
  {a ℓ : ℝ}
  (hℓ : 0 ≤ ℓ)
  {N i : ℕ}
  (hi : i ≤ N) :
  -- imply
  a ≤ pt a ℓ N i ∧ pt a ℓ N i ≤ a + ℓ := by
  -- proof
  unfold pt
  have hs := step_nonneg hℓ N
  constructor
  · nlinarith [Nat.cast_nonneg (α := ℝ) i]
  ·
    obtain hN | hN := Nat.eq_zero_or_pos N
    ·
      subst hN
      obtain rfl : i = 0 := Nat.le_zero.mp hi
      simp [hℓ]
    ·
      have h1 : (i : ℝ) * (ℓ / N) ≤ N * (ℓ / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hs
      have h2 : (N : ℝ) * (ℓ / N) = ℓ := by
        field_simp
      linarith

private lemma exists_near
  {a ℓ : ℝ}
  (hℓ : 0 ≤ ℓ)
  {N : ℕ}
  (hN : N = 0 → ℓ = 0)
  {v : ℝ}
  (hv₁ : a ≤ v)
  (hv₂ : v ≤ a + ℓ) :
  -- imply
  ∃ i ≤ N, |v - pt a ℓ N i| ≤ ℓ / N := by
  -- proof
  have hs := step_nonneg hℓ N
  obtain h0 | hpos := hs.eq_or_lt
  ·
    have hℓ0 : ℓ = 0 := by
      obtain hN0 | hNp := Nat.eq_zero_or_pos N
      · apply hN hN0
      ·
        obtain h | h := Iff.mp div_eq_zero_iff h0.symm
        · apply h
        · apply absurd h (by exact_mod_cast hNp.ne')
    refine ⟨0, Nat.zero_le _, ?_⟩
    simp only [pt, Nat.cast_zero, zero_mul, add_zero, ← h0]
    rw [abs_nonpos_iff]
    linarith
  ·
    set h := ℓ / N with hh
    have hNpos : (0 : ℝ) < N := by
      obtain hN0 | hNp := Nat.eq_zero_or_pos N
      ·
        exfalso
        rw [hN0, Nat.cast_zero, div_zero] at hh
        linarith
      · exact_mod_cast hNp
    set u := (v - a) / h with hu
    have hu0 : 0 ≤ u := div_nonneg (by linarith) hpos.le
    have huN : u ≤ N := by
      rw [hu, div_le_iff₀ hpos, hh, mul_div_cancel₀ _ hNpos.ne']
      linarith
    refine ⟨⌊u⌋₊, Nat.floor_le_of_le huN, ?_⟩
    have hfl := Nat.floor_le hu0
    have hfl' := Nat.lt_floor_add_one u
    have hkey : v - pt a ℓ N ⌊u⌋₊ = (u - ⌊u⌋₊) * h := by
      unfold pt
      rw [← hh, hu]
      field_simp
      ring
    rw [hkey, abs_of_nonneg (mul_nonneg (by linarith) hpos.le)]
    calc
      _ ≤ 1 * h := mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = h := one_mul h

private lemma walk_zero (a b : ℕ) :
  -- imply
  walk a b 0 = a := by
  -- proof
  unfold walk
  split_ifs <;> omega

private lemma walk_len (a b : ℕ) :
  -- imply
  walk a b (len a b) = b := by
  -- proof
  unfold walk len
  split_ifs <;> omega

private lemma walk_of_len_le
  {a b l : ℕ}
  (h : len a b ≤ l) :
  -- imply
  walk a b l = b := by
  -- proof
  unfold walk len at *
  split_ifs <;> omega

private lemma walk_le (a b l : ℕ) :
  -- imply
  walk a b l ≤ max a b := by
  -- proof
  unfold walk
  split_ifs <;> omega

private lemma len_le (a b : ℕ) :
  -- imply
  len a b ≤ max a b := by
  -- proof
  unfold len
  omega

private lemma walk_step (a b l : ℕ) :
  -- imply
  walk a b l ≤ walk a b (l + 1) + 1 ∧ walk a b (l + 1) ≤ walk a b l + 1 := by
  -- proof
  unfold walk
  split_ifs <;> omega

private lemma abs_cast_sub_le_one
  {p q : ℕ}
  (h : p ≤ q + 1 ∧ q ≤ p + 1) :
  -- imply
  |(p : ℝ) - q| ≤ 1 := by
  -- proof
  rw [abs_sub_le_iff]
  constructor
  ·
    have : (p : ℝ) ≤ q + 1 := by
      exact_mod_cast h.1
    linarith
  ·
    have : (q : ℝ) ≤ p + 1 := by
      exact_mod_cast h.2
    linarith

/--
[Complex_exists_grid_reProdIm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_grid_reProdIm.lean)
-/
@[path]
private lemma main
  {a₁ a₂ b₁ b₂ δ : ℝ}
  -- given
  (ha : a₁ ≤ a₂)
  (hb : b₁ ≤ b₂)
  (hδ : 0 < δ) :
  -- imply
  ∃ (m n : ℕ) (c : Fin (m + 1) × Fin (n + 1) → ℂ), (∀ i, c i ∈ Complex.reProdIm (Set.Icc a₁ a₂) (Set.Icc b₁ b₂)) ∧
    (∀ w ∈ Complex.reProdIm (Set.Icc a₁ a₂) (Set.Icc b₁ b₂), ∃ i, dist w (c i) < δ) ∧
    (∀ i j, ∃ (L : ℕ) (π : ℕ → Fin (m + 1) × Fin (n + 1)), L ≤ m + n ∧ π 0 = i ∧ π L = j ∧
      ∀ l < L, dist (c (π l)) (c (π (l + 1))) ≤ δ) := by
  -- proof
  have hℓ₁ : 0 ≤ a₂ - a₁ := by
    linarith
  have hℓ₂ : 0 ≤ b₂ - b₁ := by
    linarith
  set m := ⌈2 * (a₂ - a₁) / δ⌉₊
  set n := ⌈2 * (b₂ - b₁) / δ⌉₊
  set X : ℕ → ℝ := pt a₁ (a₂ - a₁) m
  set Y : ℕ → ℝ := pt b₁ (b₂ - b₁) n
  have hsx : (a₂ - a₁) / m ≤ δ / 2 := step_le hδ
  have hsy : (b₂ - b₁) / n ≤ δ / 2 := step_le hδ
  have hsx0 : 0 ≤ (a₂ - a₁) / m := step_nonneg hℓ₁ m
  have hsy0 : 0 ≤ (b₂ - b₁) / n := step_nonneg hℓ₂ n
  have hstepX : ∀ {p p' q : ℕ}, (p ≤ p' + 1 ∧ p' ≤ p + 1) → dist (⟨X p, Y q⟩ : ℂ) ⟨X p', Y q⟩ ≤ δ := by
    intro p p' q hpp
    rw [Complex.dist_of_im_eq (z := ⟨X p, Y q⟩) (w := ⟨X p', Y q⟩) rfl, Real.dist_eq]
    change |pt a₁ (a₂ - a₁) m p - pt a₁ (a₂ - a₁) m p'| ≤ δ
    rw [pt_sub, abs_mul, abs_of_nonneg hsx0]
    calc
      _ ≤ 1 * ((a₂ - a₁) / m) := mul_le_mul_of_nonneg_right (abs_cast_sub_le_one hpp) hsx0
      _ ≤ δ := by linarith
  have hstepY : ∀ {p q q' : ℕ}, (q ≤ q' + 1 ∧ q' ≤ q + 1) → dist (⟨X p, Y q⟩ : ℂ) ⟨X p, Y q'⟩ ≤ δ := by
    intro p q q' hqq
    rw [Complex.dist_of_re_eq (z := ⟨X p, Y q⟩) (w := ⟨X p, Y q'⟩) rfl, Real.dist_eq]
    change |pt b₁ (b₂ - b₁) n q - pt b₁ (b₂ - b₁) n q'| ≤ δ
    rw [pt_sub, abs_mul, abs_of_nonneg hsy0]
    calc
      _ ≤ 1 * ((b₂ - b₁) / n) := mul_le_mul_of_nonneg_right (abs_cast_sub_le_one hqq) hsy0
      _ ≤ δ := by linarith
  refine ⟨m, n, fun ij => ⟨X ij.1, Y ij.2⟩, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    rw [Complex.mem_reProdIm]
    simp only [Set.mem_Icc]
    have h1 := pt_mem (a := a₁) hℓ₁ (Nat.lt_succ_iff.mp hi)
    have h2 := pt_mem (a := b₁) hℓ₂ (Nat.lt_succ_iff.mp hj)
    refine ⟨⟨h1.1, ?_⟩, ⟨h2.1, ?_⟩⟩ <;> linarith [h1.2, h2.2]
  ·
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    simp only [Set.mem_Icc] at hw
    obtain ⟨i, him, hiw⟩ := exists_near (a := a₁) hℓ₁ (N := m)
      (fun h0 => ceil_eq_zero_imp hℓ₁ hδ h0) hw.1.1 (by linarith [hw.1.2])
    obtain ⟨j, hjn, hjw⟩ := exists_near (a := b₁) hℓ₂ (N := n)
      (fun h0 => ceil_eq_zero_imp hℓ₂ hδ h0) hw.2.1 (by linarith [hw.2.2])
    refine ⟨(⟨i, Nat.lt_succ_of_le him⟩, ⟨j, Nat.lt_succ_of_le hjn⟩), ?_⟩
    have hre : |w.re - X i| ≤ δ / 2 := hiw.trans hsx
    have him' : |w.im - Y j| ≤ δ / 2 := hjw.trans hsy
    rw [Complex.dist_eq_re_im, Real.sqrt_lt' hδ]
    change (w.re - X i) ^ 2 + (w.im - Y j) ^ 2 < δ ^ 2
    have h1 : (w.re - X i) ^ 2 ≤ (δ / 2) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hre 2
    have h2 : (w.im - Y j) ^ 2 ≤ (δ / 2) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) him' 2
    calc
      _ ≤ (δ / 2) ^ 2 + (δ / 2) ^ 2 := add_le_add h1 h2
      _ = δ ^ 2 / 2 := by ring
      _ < δ ^ 2 := half_lt_self (pow_pos hδ 2)
  ·
    rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩
    set L₁ := len i i' with hL₁
    set L₂ := len j j' with hL₂
    let fx : ℕ → ℕ := fun l => if l ≤ L₁ then walk i i' l else i'
    let fy : ℕ → ℕ := fun l => if l ≤ L₁ then j else walk j j' (l - L₁)
    have hfx : ∀ l, fx l < m + 1 := by
      intro l
      simp only [fx]
      split_ifs
      ·
        have := walk_le i i' l
        omega
      · omega
    have hfy : ∀ l, fy l < n + 1 := by
      intro l
      simp only [fy]
      split_ifs
      · omega
      ·
        have := walk_le j j' (l - L₁)
        omega
    have hadj : ∀ l, (fy l = fy (l + 1) ∧ (fx l ≤ fx (l + 1) + 1 ∧ fx (l + 1) ≤ fx l + 1)) ∨
        (fx l = fx (l + 1) ∧ (fy l ≤ fy (l + 1) + 1 ∧ fy (l + 1) ≤ fy l + 1)) := by
      intro l
      simp only [fx, fy, walk, hL₁, len]
      split_ifs <;> omega
    refine ⟨L₁ + L₂, fun l => (⟨fx l, hfx l⟩, ⟨fy l, hfy l⟩), ?_, ?_, ?_, ?_⟩
    ·
      have := len_le i i'
      have := len_le j j'
      omega
    ·
      simp only [fx, fy, Prod.mk.injEq, Fin.mk.injEq]
      exact ⟨by simp [walk_zero], by simp⟩
    ·
      simp only [fx, fy, Prod.mk.injEq, Fin.mk.injEq]
      constructor
      ·
        split_ifs with h
        ·
          have hL2 : L₂ = 0 := by
            omega
          apply walk_of_len_le (by omega)
        · rfl
      ·
        split_ifs with h
        ·
          have hL2 : L₂ = 0 := by
            omega
          simp only [hL₂, len] at hL2
          omega
        ·
          rw [Nat.add_sub_cancel_left]
          apply walk_len j j'
    ·
      intro l _
      obtain ⟨hy, hx⟩ | ⟨hx, hy⟩ := hadj l
      ·
        change dist (⟨X (fx l), Y (fy l)⟩ : ℂ) ⟨X (fx (l + 1)), Y (fy (l + 1))⟩ ≤ δ
        rw [← hy]
        apply hstepX hx
      ·
        change dist (⟨X (fx l), Y (fy l)⟩ : ℂ) ⟨X (fx (l + 1)), Y (fy (l + 1))⟩ ≤ δ
        rw [← hx]
        apply hstepY hy


-- created on 2026-10-20

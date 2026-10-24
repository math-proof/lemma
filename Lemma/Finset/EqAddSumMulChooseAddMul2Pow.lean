import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma walk_eq_zero_of_lt
  {q : ℕ}
  {W : ℕ → ℕ → ℕ}
  -- given
  (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
  (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
  -- imply
  ∀ k d : ℕ, k < d → W k d = 0 := by
  -- proof
  intro k
  induction k
  ·
    intro d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    apply h0s d'
  ·
    rename_i k ih
    intro d hd
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [hstep, ih d' (by omega), ih (d' + 2) (by omega), mul_zero, add_zero]

private lemma telescope
  {q : ℤ}
  {A : ℕ → ℤ} :
  ∀ n : ℕ, (q + 1) * A 0 + ∑ r ∈ Finset.range (n + 1), (A r + q * A (r + 1)) * (q ^ (r + 1) - q ^ r) = 2 * q * (A 0 + ∑ r ∈ Finset.range n, A (r + 1) * (q ^ (r + 1) - q ^ r)) + q * A (n + 1) * (q ^ (n + 1) - q ^ n) := by
  intro n
  induction n
  ·
    simp
    ring
  ·
    rename_i n ih
    rw [Finset.sum_range_succ, ← add_assoc, ih, Finset.sum_range_succ]
    ring

private lemma sum_shift_split
  {q : ℤ}
  {B C : ℕ → ℤ}
  {μ : ℕ} :
  ∑ r ∈ Finset.range μ, (B r + q * C r) * (q ^ (r + 1) - q ^ r) = ∑ r ∈ Finset.range μ, B r * (q ^ (r + 1) - q ^ r) + q * ∑ r ∈ Finset.range μ, C r * (q ^ (r + 1) - q ^ r) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

private lemma helper_main
  {q : ℕ}
  {W : ℕ → ℕ → ℕ}
  -- given
  (h00 : W 0 0 = 1)
  (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
  (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
  (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
  -- imply
  ∀ k : ℕ, ∀ d μ : ℕ, d + 2 * μ = k → (W k d : ℤ) + ∑ r ∈ Finset.range μ, (W k (d + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) = ((k.choose μ : ℕ) : ℤ) * (q : ℤ) ^ μ := by
  -- proof
  have hvan := walk_eq_zero_of_lt h0s hstep
  intro k
  induction k
  ·
    intro d μ h
    have hμ : μ = 0 := by omega
    have hd : d = 0 := by omega
    subst hμ hd
    simp [h00]
  ·
    rename_i k ih
    intro d μ h
    if hd0 : d = 0 then
      subst hd0
      obtain ⟨μ', rfl⟩ : ∃ μ' : ℕ, μ = μ' + 1 := ⟨μ - 1, by omega⟩
      have hk : k = 2 * μ' + 1 := by omega
      have e0 : (W (k + 1) 0 : ℤ) = ((q : ℤ) + 1) * W k 1 := by
        rw [hroot]
        push_cast
        ring
      have e2 : ∀ r : ℕ, (W (k + 1) (0 + 2 * (r + 1)) : ℤ) = (W k (2 * r + 1) : ℤ) + (q : ℤ) * W k (2 * (r + 1) + 1) := by
        intro r
        rw [show 0 + 2 * (r + 1) = (2 * r + 1) + 1 by ring, hstep, show 2 * r + 1 + 2 = 2 * (r + 1) + 1 by ring]
        push_cast
        ring
      rw [e0, Finset.sum_congr rfl (fun r _ => by rw [e2 r])]
      have hT := telescope (q := (q : ℤ)) (A := fun r => (W k (2 * r + 1) : ℤ)) μ'
      simp only [Nat.mul_zero, zero_add] at hT
      rw [hT, hvan k (2 * (μ' + 1) + 1) (by omega)]
      have hih := ih 1 μ' (by omega)
      have hre : ∀ r : ℕ, (1 + 2 * (r + 1)) = 2 * (r + 1) + 1 := fun r => by ring
      simp only [hre] at hih
      rw [hih, hk]
      rw [show 2 * μ' + 1 + 1 = (2 * μ' + 1) + 1 by rfl, Nat.choose_succ_succ', Nat.choose_symm_half]
      push_cast
      simp only [pow_succ]
      ring
    else
      obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      have hk : d' + 2 * μ = k := by omega
      have e1 : (W (k + 1) (d' + 1) : ℤ) = (W k d' : ℤ) + (q : ℤ) * W k (d' + 2) := by
        rw [hstep]
        push_cast
        ring
      have e2 : ∀ r : ℕ, (W (k + 1) (d' + 1 + 2 * (r + 1)) : ℤ) = (W k (d' + 2 * (r + 1)) : ℤ) + (q : ℤ) * W k (d' + 2 + 2 * (r + 1)) := by
        intro r
        rw [show d' + 1 + 2 * (r + 1) = (d' + 2 * (r + 1)) + 1 by ring, hstep, show d' + 2 * (r + 1) + 2 = d' + 2 + 2 * (r + 1) by ring]
        push_cast
        ring
      rw [e1, Finset.sum_congr rfl (fun r _ => by rw [e2 r]), sum_shift_split]
      have hA := ih d' μ hk
      if hμ0 : μ = 0 then
        subst hμ0
        have hA' : (W k d' : ℤ) = 1 := by simpa using hA
        simp [hvan k (d' + 2) (by omega), hA']
      else
        obtain ⟨μ', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hμ0
        have hB := ih (d' + 2) μ' (by omega)
        rw [Finset.sum_range_succ (fun r => (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)), hvan k (d' + 2 + 2 * (μ' + 1)) (by omega)]
        have hre : ∀ r : ℕ, d' + 2 + 2 * (r + 1) = d' + 2 * (r + 1) + 2 := fun r => by ring
        have : (W k d' : ℤ) + (q : ℤ) * W k (d' + 2) + (∑ r ∈ Finset.range (μ' + 1), (W k (d' + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) + (q : ℤ) * (∑ r ∈ Finset.range μ', (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) + ((0 : ℕ) : ℤ) * ((q : ℤ) ^ (μ' + 1) - (q : ℤ) ^ μ'))) = ((W k d' : ℤ) + ∑ r ∈ Finset.range (μ' + 1), (W k (d' + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)) + (q : ℤ) * ((W k (d' + 2) : ℤ) + ∑ r ∈ Finset.range μ', (W k (d' + 2 + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r)) := by
          push_cast
          ring
        rw [this, hA, hB, Nat.choose_succ_succ']
        push_cast
        rw [Nat.succ_eq_add_one, Nat.add_comm 1 μ']
        simp only [pow_succ]
        ring

/--
[HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HeckeTreeWalk_cast_walkCount_add_sum_mul_pow_sub_pow_eq_choose_mul_pow.lean)
-/
@[path]
private lemma main
  {q : ℕ}
  {W : ℕ → ℕ → ℕ}
  {d μ : ℕ}
  -- given
  (h00 : W 0 0 = 1)
  (h0s : ∀ d : ℕ, W 0 (d + 1) = 0)
  (hroot : ∀ k : ℕ, W (k + 1) 0 = (q + 1) * W k 1)
  (hstep : ∀ k d : ℕ, W (k + 1) (d + 1) = W k d + q * W k (d + 2)) :
  -- imply
  (W (d + 2 * μ) d : ℤ) + ∑ r ∈ Finset.range μ, (W (d + 2 * μ) (d + 2 * (r + 1)) : ℤ) * ((q : ℤ) ^ (r + 1) - (q : ℤ) ^ r) = (((d + 2 * μ).choose μ : ℕ) : ℤ) * (q : ℤ) ^ μ := by
  -- proof
  apply helper_main h00 h0s hroot hstep (d + 2 * μ) d μ rfl


-- created on 2026-10-20

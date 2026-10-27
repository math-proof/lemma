import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsLocalRing A]
  (hH : ∀ x : A, (∀ n : ℕ, x ∈ maximalIdeal A ^ n) → x = 0)
  {a d : A} {q : ℕ} (had : IsUnit (a - (q : A) * d)) (hda : IsUnit (d - (q : A) * a))
  {N : Matrix (Fin 2) (Fin 2) A} (hN : ∀ i j, N i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ maximalIdeal A)
  (hrel : Matrix.diagonal (Matrix.vecCons a (Matrix.vecCons d Matrix.vecEmpty)) * N = N ^ q * Matrix.diagonal (Matrix.vecCons a (Matrix.vecCons d Matrix.vecEmpty))) :
  -- imply
  N 0 1 = 0 ∧ N 1 0 = 0 := by
  -- proof
  set 𝔪 := maximalIdeal A with h𝔪
  have h00 : N 0 0 - 1 ∈ 𝔪 := by
    have h := hN 0 0
    simp at h
    apply h
  have h11 : N 1 1 - 1 ∈ 𝔪 := by
    have h := hN 1 1
    simp at h
    apply h
  have h01m : N 0 1 ∈ 𝔪 := by
    have h := hN 0 1
    simp at h
    apply h
  have h10m : N 1 0 ∈ 𝔪 := by
    have h := hN 1 0
    simp at h
    apply h
  have hmul : ∀ (n : ℕ) (x y : A), x ∈ 𝔪 → y ∈ 𝔪 ^ n → x * y ∈ 𝔪 ^ (n + 1) := fun n x y hx hy => by
    rw [pow_succ']
    apply Ideal.mul_mem_mul hx hy
  have step : ∀ n : ℕ, N 0 1 ∈ 𝔪 ^ n → N 1 0 ∈ 𝔪 ^ n → N 0 1 ∈ 𝔪 ^ (n + 1) ∧ N 1 0 ∈ 𝔪 ^ (n + 1) := by
    intro n h01 h10
    have hpow : ∀ j : ℕ, ((N ^ j) 0 0 - 1 ∈ 𝔪 ∧ (N ^ j) 1 1 - 1 ∈ 𝔪) ∧ ((N ^ j) 0 1 - (j : A) * N 0 1 ∈ 𝔪 ^ (n + 1) ∧ (N ^ j) 1 0 - (j : A) * N 1 0 ∈ 𝔪 ^ (n + 1)) := by
      intro j
      induction j
      ·
        simp
      ·
        rename_i j ih
        obtain ⟨⟨i00, i11⟩, i01, i10⟩ := ih
        have e00 : (N ^ (j + 1)) 0 0 = (N ^ j) 0 0 * N 0 0 + (N ^ j) 0 1 * N 1 0 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e11 : (N ^ (j + 1)) 1 1 = (N ^ j) 1 0 * N 0 1 + (N ^ j) 1 1 * N 1 1 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e01 : (N ^ (j + 1)) 0 1 = (N ^ j) 0 0 * N 0 1 + (N ^ j) 0 1 * N 1 1 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have e10 : (N ^ (j + 1)) 1 0 = (N ^ j) 1 0 * N 0 0 + (N ^ j) 1 1 * N 1 0 := by
          rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
        have j01 : (N ^ j) 0 1 ∈ 𝔪 ^ n := by
          have : (N ^ j) 0 1 = ((N ^ j) 0 1 - (j : A) * N 0 1) + (j : A) * N 0 1 := by
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) i01) (Ideal.mul_mem_left _ _ h01)
        have j10 : (N ^ j) 1 0 ∈ 𝔪 ^ n := by
          have : (N ^ j) 1 0 = ((N ^ j) 1 0 - (j : A) * N 1 0) + (j : A) * N 1 0 := by
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ n) i10) (Ideal.mul_mem_left _ _ h10)
        have j01m : (N ^ j) 0 1 ∈ 𝔪 := by
          have : (N ^ j) 0 1 = ((N ^ j) 0 1 - (j : A) * N 0 1) + (j : A) * N 0 1 := by
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero n) i01) (Ideal.mul_mem_left _ _ h01m)
        have j10m : (N ^ j) 1 0 ∈ 𝔪 := by
          have : (N ^ j) 1 0 = ((N ^ j) 1 0 - (j : A) * N 1 0) + (j : A) * N 1 0 := by
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.pow_le_self (Nat.succ_ne_zero n) i10) (Ideal.mul_mem_left _ _ h10m)
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        ·
          have : (N ^ (j + 1)) 0 0 - 1 = ((N ^ j) 0 0 - 1) * N 0 0 + (N 0 0 - 1) + (N ^ j) 0 1 * N 1 0 := by
            rw [e00]
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i00) h00) (Ideal.mul_mem_left _ _ h10m)
        ·
          have : (N ^ (j + 1)) 1 1 - 1 = (N ^ j) 1 0 * N 0 1 + (((N ^ j) 1 1 - 1) * N 1 1 + (N 1 1 - 1)) := by
            rw [e11]
            ring
          rw [this]
          apply Ideal.add_mem _ (Ideal.mul_mem_left _ _ h01m) (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i11) h11)
        ·
          have : (N ^ (j + 1)) 0 1 - ((j + 1 : ℕ) : A) * N 0 1 = ((N ^ j) 0 0 - 1) * N 0 1 + ((N ^ j) 0 1 - (j : A) * N 0 1) * N 1 1 + ((j : A) * N 0 1) * (N 1 1 - 1) := by
            rw [e01]
            push_cast
            ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ (hmul n _ _ i00 h01) (Ideal.mul_mem_right _ _ i01)) ?_
          rw [mul_comm]
          apply hmul n _ _ h11 (Ideal.mul_mem_left _ _ h01)
        ·
          have : (N ^ (j + 1)) 1 0 - ((j + 1 : ℕ) : A) * N 1 0 = ((N ^ j) 1 0 - (j : A) * N 1 0) * N 0 0 + ((j : A) * N 1 0) * (N 0 0 - 1) + ((N ^ j) 1 1 - 1) * N 1 0 := by
            rw [e10]
            push_cast
            ring
          rw [this]
          refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ i10) ?_) (hmul n _ _ i11 h10)
          rw [mul_comm]
          apply hmul n _ _ h00 (Ideal.mul_mem_left _ _ h10)
    obtain ⟨-, q01, q10⟩ := hpow q
    have r01 : a * N 0 1 = (N ^ q) 0 1 * d := by
      have h := congrFun (congrFun hrel 0) 1
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      apply h
    have r10 : d * N 1 0 = (N ^ q) 1 0 * a := by
      have h := congrFun (congrFun hrel 1) 0
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      apply h
    constructor
    ·
      have key : (a - (q : A) * d) * N 0 1 = ((N ^ q) 0 1 - (q : A) * N 0 1) * d := by
        rw [sub_mul, r01]
        ring
      apply (Ideal.unit_mul_mem_iff_mem _ had).mp _
      rw [key]
      apply Ideal.mul_mem_right _ _ q01
    ·
      have key : (d - (q : A) * a) * N 1 0 = ((N ^ q) 1 0 - (q : A) * N 1 0) * a := by
        rw [sub_mul, r10]
        ring
      apply (Ideal.unit_mul_mem_iff_mem _ hda).mp _
      rw [key]
      apply Ideal.mul_mem_right _ _ q10
  have hall : ∀ n : ℕ, N 0 1 ∈ 𝔪 ^ n ∧ N 1 0 ∈ 𝔪 ^ n := by
    intro n
    induction n
    ·
      simp
    ·
      rename_i n ih
      apply step n ih.1 ih.2
  exact ⟨hH _ fun n => (hall n).1, hH _ fun n => (hall n).2⟩


-- created on 2026-10-20

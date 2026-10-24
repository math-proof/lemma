import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


universe u

variable {S : Type u} [CommRing S] (p : ℕ) [Fact p.Prime]
private lemma mem_of_pow_mem
  (hred : IsReduced (S ⧸ Ideal.span {(p : S)})) {a : S} {k : ℕ} (_ : k ≠ 0)
  (ha : a ^ k ∈ Ideal.span {(p : S)}) :
  a ∈ Ideal.span {(p : S)} := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at ha ⊢
  rw [map_pow] at ha
  refine IsReduced.eq_zero _ ⟨k, ha⟩
private lemma pow_le_pow_pow
  (N : ℕ) :
  N ≤ p ^ N :=
  (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out)).le
private lemma helper_main
  (hp : (p : S) ∈ nonZeroDivisors S) (hred : IsReduced (S ⧸ Ideal.span {(p : S)})) :
  ∀ (N : ℕ) (z : ℕ → S),
    (∑ j ∈ Finset.range N, (p : S) ^ j * z j ^ p ^ (N - 1 - j)) ∈ Ideal.span {(p : S) ^ N} →
    ∀ j, j < N → z j ∈ Ideal.span {(p : S)} := by
  intro N
  induction N
  ·
    intro z _ j hj
    refine absurd hj (Nat.not_lt_zero _)
  ·
    rename_i N ih
    intro z hz j hj
    have h0 : z 0 ∈ Ideal.span {(p : S)} := by
      have hsum : (∑ j ∈ Finset.range (N + 1), (p : S) ^ j * z j ^ p ^ (N + 1 - 1 - j)) ∈ Ideal.span {(p : S)} := by
        refine Ideal.span_singleton_le_span_singleton.2 ⟨(p : S) ^ N, by ring⟩ hz
      rw [Finset.sum_range_succ'] at hsum
      have hrest : (∑ j ∈ Finset.range N, (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) ∈
        Ideal.span {(p : S)} := by
        refine Ideal.sum_mem _ fun j _ => ?_
        rw [pow_succ', mul_assoc]
        refine Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have this := Ideal.sub_mem _ hsum hrest
      rw [add_sub_cancel_left, pow_zero, one_mul] at this
      if hN : p ^ (N + 1 - 1 - 0) = 0 then
        refine absurd hN (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))
      else
        refine mem_of_pow_mem p hred hN this
    cases Nat.eq_zero_or_pos j
    ·
      rename_i hzj
      subst hzj
      refine h0
    ·
      rename_i hjpos
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h0
      have hz0 : (p : S) ^ 0 * z 0 ^ p ^ (N + 1 - 1 - 0) ∈ Ideal.span {(p : S) ^ (N + 1)} := by
        rw [pow_zero, one_mul, ← ht, mul_pow]
        simp only [Nat.add_sub_cancel, Nat.sub_zero]
        refine Ideal.mul_mem_left _ _ (Ideal.span_singleton_le_span_singleton.2 ?_ (Ideal.mem_span_singleton_self _))
        refine pow_dvd_pow _ (Nat.lt_pow_self (Nat.Prime.one_lt Fact.out))
      have hrest : (∑ j ∈ Finset.range N, (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) ∈
        Ideal.span {(p : S) ^ (N + 1)} := by
        have this := Ideal.sub_mem _ hz hz0
        rw [Finset.sum_range_succ', add_sub_cancel_right] at this
        refine this
      have hfac : (∑ j ∈ Finset.range N, (p : S) ^ (j + 1) * z (j + 1) ^ p ^ (N + 1 - 1 - (j + 1))) =
          (p : S) * ∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : N + 1 - 1 - (j + 1) = N - 1 - j := by
          omega
        rw [this, pow_succ']
        ring
      rw [hfac] at hrest
      have hrest' : (∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j)) ∈ Ideal.span {(p : S) ^ N} := by
        obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hrest
        refine Ideal.mem_span_singleton'.2 ⟨s, ?_⟩
        have : (p : S) * (s * (p : S) ^ N) =
            (p : S) * ∑ j ∈ Finset.range N, (p : S) ^ j * z (j + 1) ^ p ^ (N - 1 - j) := by
          rw [← hs]
          ring
        refine (mul_cancel_left_mem_nonZeroDivisors hp).1 this
      have ihj := ih (fun j => z (j + 1)) hrest' (j - 1) (by omega)
      have : j - 1 + 1 = j := by
        omega
      simp [this] at ihj
      refine ihj
/--
[WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WittVector_coeff_mem_span_of_ghostComponent_mem_span_pow_of_isReduced.lean)
-/
@[path]
private lemma main
  (hp : (p : S) ∈ nonZeroDivisors S)
  (hred : IsReduced (S ⧸ Ideal.span {(p : S)}))
  (z : WittVector p S) (N : ℕ)
  (hz : WittVector.ghostComponent (N - 1) z ∈ Ideal.span {(p : S) ^ N}) :
  -- imply
  ∀ j : ℕ, j < N → z.coeff j ∈ Ideal.span {(p : S)} := by
  -- proof
  intro j hj
  cases Nat.eq_zero_or_pos N
  ·
    rename_i hzN
    subst hzN
    refine absurd hj (Nat.not_lt_zero _)
  ·
    have hN : N - 1 + 1 = N := by
      omega
    refine helper_main p hp hred N (fun j => z.coeff j) ?_ j hj
    have h := hz
    rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow, map_sum, hN] at h
    simp only [map_mul, map_pow, MvPolynomial.aeval_X, map_natCast] at h
    refine h


-- created on 2026-10-20

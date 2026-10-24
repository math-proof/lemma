import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


universe u

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
private lemma ghost_eq_sum
  (k : ℕ) (x : WittVector p R) :
  WittVector.ghostComponent k x =
    ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]
private lemma pow_sub_pow_mem
  {a b : R} (h : a - b ∈ Ideal.span {(p : R)}) (m : ℕ) :
  a ^ p ^ m - b ^ p ^ m ∈ Ideal.span {(p : R) ^ (m + 1)} := by
  have h' := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.1 h) m
  rw [Ideal.mem_span_singleton]
  exact_mod_cast h'
private lemma ghost_succ_eq
  (k : ℕ) (x : WittVector p R) :
  WittVector.ghostComponent (k + 1) x =
    ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) +
      (p : R) ^ (k + 1) * x.coeff (k + 1) := by
  rw [ghost_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
private lemma ghost_succ_sub_mem
  (σ : R →+* R) (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
  (x : WittVector p R) (k : ℕ) :
  WittVector.ghostComponent (k + 1) x - σ (WittVector.ghostComponent k x) ∈
    Ideal.span {(p : R) ^ (k + 1)} := by
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) - σ ((p : R) ^ i * x.coeff i ^ p ^ (k - i)) ∈
        Ideal.span {(p : R) ^ (k + 1)} := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_natCast, map_pow, ← mul_sub,
      show k + 1 - i = k - i + 1 by omega, pow_succ' (p : ℕ) (k - i), pow_mul]
    have hsub : x.coeff i ^ p - σ (x.coeff i) ∈ Ideal.span {(p : R)} := by
      rw [← neg_sub]
      refine (Ideal.neg_mem_iff _).2 (hσ _)
    have hd := pow_sub_pow_mem (p := p) (a := x.coeff i ^ p) (b := σ (x.coeff i)) hsub (k - i)
    rw [Ideal.mem_span_singleton] at hd ⊢
    have hpk : (p : R) ^ (k + 1) = (p : R) ^ i * (p : R) ^ (k - i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpk]
    refine mul_dvd_mul_left _ hd
  rw [ghost_succ_eq, ghost_eq_sum, map_sum, add_sub_right_comm, ← Finset.sum_sub_distrib]
  refine Ideal.add_mem _ (Ideal.sum_mem _ hterm)
    (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
private lemma exists_ghost_eq
  (σ : R →+* R) (hσ : ∀ a : R, σ a - a ^ p ∈ Ideal.span {(p : R)})
  (n : ℕ) (g : ℕ → R)
  (hg : ∀ k : ℕ, k + 1 < n → g (k + 1) - σ (g k) ∈ Ideal.span {(p : R) ^ (k + 1)}) :
  ∃ x : WittVector p R, ∀ k < n, WittVector.ghostComponent k x = g k := by
  induction n
  · refine ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  ·
    rename_i n ih
    obtain ⟨x, hx⟩ := ih (fun k hk => hg k (by omega))
    have hdef : g n - ∑ i ∈ Finset.range n, (p : R) ^ i * x.coeff i ^ p ^ (n - i) ∈
      Ideal.span {(p : R) ^ n} := by
      cases n
      · simp
      ·
        rename_i k
        have h1 := hg k (by omega)
        have h3 := ghost_succ_sub_mem σ hσ x k
        rw [hx k (by omega)] at h3
        have key : g (k + 1) - ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k + 1 - i) =
            (g (k + 1) - σ (g k)) - (WittVector.ghostComponent (k + 1) x - σ (g k)) +
              (p : R) ^ (k + 1) * x.coeff (k + 1) := by
          rw [ghost_succ_eq]
          ring
        rw [key]
        refine Ideal.add_mem _ (Ideal.sub_mem _ h1 h3)
          (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hdef
    refine ⟨WittVector.mk p (fun i => if i = n then c else x.coeff i), fun k hk => ?_⟩
    if hkn : k < n then
      rw [← hx k hkn, ghost_eq_sum, ghost_eq_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [WittVector.coeff_mk]
      rw [ite_eq_right (show i ≠ n by omega)]
    else
      have hkn' : k = n := by omega
      rw [hkn', ghost_eq_sum, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
      simp only [WittVector.coeff_mk, ite_true]
      have hS : ∑ i ∈ Finset.range n, (p : R) ^ i * (if i = n then c else x.coeff i) ^ p ^ (n - i) =
          ∑ i ∈ Finset.range n, (p : R) ^ i * x.coeff i ^ p ^ (n - i) :=
        Finset.sum_congr rfl fun i hi => by
          have hine : i ≠ n := by
            intro h
            rw [Finset.mem_range] at hi
            omega
          rw [ite_eq_right hine]
      rw [hS, mul_comm ((p : R) ^ n) c, hc]
      ring
private lemma coeff_eq_of_ghost_eq
  (hpR : (p : R) ∈ nonZeroDivisors R) (n : ℕ) (x y : WittVector p R)
  (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
  ∀ k < n, x.coeff k = y.coeff k := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk
  have hk' := h k hk
  rw [ghost_eq_sum, ghost_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self, pow_zero,
    pow_one, pow_one] at hk'
  have hS : ∑ i ∈ Finset.range k, (p : R) ^ i * x.coeff i ^ p ^ (k - i) =
      ∑ i ∈ Finset.range k, (p : R) ^ i * y.coeff i ^ p ^ (k - i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [ih i (Finset.mem_range.1 hi) (lt_trans (Finset.mem_range.1 hi) hk)]
  rw [hS, add_right_inj] at hk'
  refine sub_eq_zero.1
    ((mem_nonZeroDivisors_iff.1 (pow_mem hpR k)).1 _ (by rw [mul_sub, hk', sub_self]))
/--
[WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
  (n : ℕ) (x y : WittVector p R)
  (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
  -- imply
  ∀ k < n, x.coeff k = y.coeff k :=
  coeff_eq_of_ghost_eq hp n x y h


-- created on 2026-10-21

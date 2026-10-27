import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Catalan.KnuthCatalanLogSq


section

open scoped BigOperators

namespace MetaMathlibExt

theorem harmDiff_nonneg (n : ℕ) : 0 ≤ harmDiff n := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have h : (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)
      ≤ (∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
  simp only [harmDiff]
  linarith [h]

theorem harmDiff_le (n : ℕ) : harmDiff n ≤ (n : ℝ) := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hinter : Finset.range (n + 1) ∩ Finset.range (2 * (n + 1) - 1)
      = Finset.range (n + 1) := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_range]
    omega
  have hcard : (Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card = n := by
    rw [Finset.card_sdiff, hinter, Finset.card_range, Finset.card_range]
    omega
  have hsplit : harmDiff n
      = ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹ := by
    simp only [harmDiff]
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  rw [hsplit]
  calc ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹
      ≤ ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), 1 :=
        Finset.sum_le_sum (fun k _ => inv_le_one_of_one_le₀ (by
          have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
          linarith [hk]))
    _ = ((Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (n : ℝ) := by rw [hcard]

theorem harmD_zero : harmD 0 = 0 := by
  have e1 : 2 * (0 + 1) - 1 = 1 := by norm_num
  have e2 : 0 + 1 = 1 := by norm_num
  simp only [harmD, harmDiff]
  rw [e1, e2, sub_self, mul_zero]

theorem summable_dnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖harmD n * y ^ n‖) := by
  have hM := majorant_summable |y| hy (abs_nonneg y)
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hM
  intro n
  have hcb : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) := by positivity
  have hΔ := harmDiff_nonneg n
  have hΔle := harmDiff_le n
  have hC := cb_le_four_pow_real (n + 1)
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hDnn : 0 ≤ harmD n := by
    simp only [harmD]
    exact mul_nonneg hcb hΔ
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hDnn]
  have s1 : harmD n ≤ 4 ^ (n + 1) * (n : ℝ) := by
    simp only [harmD]
    exact mul_le_mul hC hΔle hΔ (by positivity)
  have step1 : harmD n * |y| ^ n ≤ (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n :=
    mul_le_mul_of_nonneg_right s1 (pow_nonneg (abs_nonneg y) n)
  have step2 : (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n
      ≤ ((n : ℝ) + 1) * 4 ^ (n + 1) * |y| ^ n * 5 := by
    have e : ((n : ℝ) + 1) * 4 ^ (n + 1) * |y| ^ n * 5 - (4 ^ (n + 1) * (n : ℝ)) * |y| ^ n
        = (4 ^ (n + 1) * |y| ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by ring
    have hpos : (0 : ℝ) ≤ (4 ^ (n + 1) * |y| ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by
      apply mul_nonneg
      · exact mul_nonneg (by positivity) (pow_nonneg (abs_nonneg y) n)
      · linarith [hnn]
    linarith [hpos]
  linarith [step1, step2]

theorem summable_Hnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1)‖) := by
  have hB := summable_cbnorm y hy
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ (hB.mul_left |y|)
  intro n
  have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1) := by positivity
  have hnn3 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
  have h1 : ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1)‖
      = ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ (n + 1) := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
  rw [h1]
  have hle : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1))
      ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by
    apply div_le_self (by positivity)
    have h1le : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    exact h1le
  have e : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ (n + 1)
      = |y| * (((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ n) := by ring
  have h2 : (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n
      = ‖(Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn3]
  have h3 : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * |y| ^ n
      ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n :=
    mul_le_mul_of_nonneg_right hle (pow_nonneg (abs_nonneg y) n)
  rw [e, ← h2]
  exact mul_le_mul_of_nonneg_left h3 (abs_nonneg y)

/-- Shifted coefficient identity: twice the H-B convolution coefficient
    is the next d-coefficient. -/
theorem hper_sum (N : ℕ) :
    2 * (∑ k ∈ Finset.range (N + 1),
      (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
        * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = harmD (N + 1) := by
  have hC := conv_for_square (N + 1)
  have hbridge : (∑ k ∈ Finset.range (N + 1),
        (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = ∑ k ∈ Finset.range (N + 1 + 1),
        ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ))
          * ((Nat.centralBinom (N + 1 - k + 1) : ℝ) / 2)) := by
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.centralBinom_zero, Nat.cast_zero, mul_zero, div_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have e : N + 1 - (k + 1) + 1 = N - k + 1 := by
      have hkn : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega
    rw [e]
    push_cast
    rw [div_div]
  rw [hbridge]
  simp only [harmD, harmDiff]
  exact hC

/-- Termwise derivative of the integrated d-series on a ball. -/
theorem K_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt
      (fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (∑' n, harmD n * y ^ n) y := by
  have hU := majorant_summable R hR4 hR0.le
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hzero : (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  have hS0 : Summable (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) := by
    rw [hzero]
    exact summable_zero
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖(harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)‖
        ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
    intro n t ht
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hDnn : 0 ≤ harmD n := by
      simp only [harmD]
      exact mul_nonneg (by positivity) (harmDiff_nonneg n)
    have hcancel : (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
        = harmD n * t ^ n := by
      have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hcancel, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hDnn]
    have hpow : |t| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg t) htb n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have s1 : harmD n ≤ 4 ^ (n + 1) * (n : ℝ) := by
      simp only [harmD]
      exact mul_le_mul (cb_le_four_pow_real _) (harmDiff_le n) (harmDiff_nonneg n) (by positivity)
    have step1 : harmD n * |t| ^ n ≤ (4 ^ (n + 1) * (n : ℝ)) * R ^ n :=
      mul_le_mul s1 hpow (pow_nonneg (abs_nonneg t) _) (by positivity)
    have step2 : (4 ^ (n + 1) * (n : ℝ)) * R ^ n
        ≤ ((n : ℝ) + 1) * 4 ^ (n + 1) * R ^ n * 5 := by
      have e : ((n : ℝ) + 1) * 4 ^ (n + 1) * R ^ n * 5 - (4 ^ (n + 1) * (n : ℝ)) * R ^ n
          = (4 ^ (n + 1) * R ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by ring
      have hpos : (0 : ℝ) ≤ (4 ^ (n + 1) * R ^ n) * (((n : ℝ) + 1) * 5 - (n : ℝ)) := by
        apply mul_nonneg
        · exact mul_nonneg (by positivity) (pow_nonneg hR0.le n)
        · linarith [hnn]
      linarith [hpos]
    linarith [step1, step2]
  have hmain : HasDerivAt
      (fun z => ∑' n, (harmD n / ((n : ℝ) + 1)) * z ^ (n + 1))
      (∑' n, (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => by
        have h1 := ((hasDerivAt_pow (n + 1) t).const_mul (harmD n / ((n : ℝ) + 1)))
        have e1 : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have e2 : n + 1 - 1 = n := by omega
        rw [e1, e2] at h1
        exact h1)
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hcongr : (∑' n, (harmD n / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      = ∑' n, harmD n * y ^ n := by
    apply tsum_congr
    intro n
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hcongr] at hmain
  exact hmain

/-- Cauchy product: the H-series times the b-series is the half-d-series. -/
theorem H_mul_B (y : ℝ) (hy : |y| < 1 / 4) :
    (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1))
      * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
    = ∑' N, (harmD (N + 1) / 2) * y ^ (N + 1) := by
  have hHn := summable_Hnorm y hy
  have hBn := summable_cbnorm y hy
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hHn hBn]
  apply tsum_congr
  intro N
  have hpow : ∀ k ∈ Finset.range (N + 1), y ^ (k + 1) * y ^ (N - k) = y ^ (N + 1) := by
    intro k hk
    have hkn : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [← pow_add]
    congr 1
    omega
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1)) * y ^ (k + 1))
        * (((Nat.centralBinom (N - k + 1) : ℝ) / 2) * y ^ (N - k))
      = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * y ^ (N + 1) := by
    intro k hk
    calc (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1)) * y ^ (k + 1))
            * (((Nat.centralBinom (N - k + 1) : ℝ) / 2) * y ^ (N - k))
        = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
            * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * (y ^ (k + 1) * y ^ (N - k)) := by
          ring
      _ = ((((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2))) * y ^ (N + 1) := by
          rw [hpow k hk]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hS : (∑ k ∈ Finset.range (N + 1),
        (((Nat.centralBinom (k + 1) : ℝ) / 2 / ((k : ℝ) + 1))
          * ((Nat.centralBinom (N - k + 1) : ℝ) / 2)))
      = harmD (N + 1) / 2 := by
    have hper := hper_sum N
    linarith [hper]
  rw [hS]

/-- Derivative of the squared log-Catalan series. -/
theorem M_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) ^ 2)
      (2 * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)) y := by
  have hL := L_hasDerivAt R hR4 hR0 hR8 y hy
  have h2 := hL.mul hL
  have heq : (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
          * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        + (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
          * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
      = 2 * (Real.log (∑' n, (catalan n : ℝ) * y ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) := by ring
  rw [heq] at h2
  have hEq : ∀ t, (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) ^ 2
      = ((fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))) t := by
    intro t
    rw [Pi.mul_apply, pow_two]
  exact h2.congr_of_eventuallyEq (Filter.Eventually.of_forall hEq)

theorem K_tsum_zero : (∑' n, (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = 0 := by
  have hzero : (fun n => (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [hzero]
  exact tsum_zero

/-- The squared log-Catalan series equals the integrated d-series on the ball. -/
theorem M_eq_K (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    (Real.log (∑' n, (catalan n : ℝ) * y ^ n)) ^ 2
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * y ^ (n + 1) := by
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hLH : ∀ t ∈ Metric.ball (0 : ℝ) R,
      Real.log (∑' n, (catalan n : ℝ) * t ^ n)
        = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1) :=
    fun t ht => L_eq_H R hR4 hR0 hR8 t ht
  have hHB : ∀ t ∈ Metric.ball (0 : ℝ) R,
      (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
      = ∑' N, (harmD (N + 1) / 2) * t ^ (N + 1) := by
    intro t ht
    have ht4 : |t| < 1 / 4 := lt_trans (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h) hR4
    exact H_mul_B t ht4
  have hMD : ∀ t ∈ Metric.ball (0 : ℝ) R,
      2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
      = ∑' n, harmD n * t ^ n := by
    intro t ht
    have ht4 : |t| < 1 / 4 := lt_trans (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h) hR4
    have hDsumm : Summable (fun n => harmD n * t ^ n) := (summable_dnorm t ht4).of_norm
    have hDshift : (∑' n, harmD n * t ^ n) = ∑' n, harmD (n + 1) * t ^ (n + 1) := by
      rw [hDsumm.tsum_eq_zero_add]
      have hd0 : harmD 0 * t ^ 0 = 0 := by rw [harmD_zero, zero_mul]
      simp only [hd0, zero_add]
    calc 2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
            * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)
        = 2 * ((∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
            * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)) := by
          rw [hLH t ht]; ring
      _ = 2 * (∑' n, (harmD (n + 1) / 2) * t ^ (n + 1)) := by rw [hHB t ht]
      _ = ∑' n, harmD (n + 1) * t ^ (n + 1) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro N
          ring
      _ = ∑' n, harmD n * t ^ n := hDshift.symm
  have hM' : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2)
        (2 * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
          * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n)) t :=
    fun t ht => M_hasDerivAt R hR4 hR0 hR8 t ht
  have hK' : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt
        (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1))
        (∑' n, harmD n * t ^ n) t :=
    fun t ht => K_hasDerivAt R hR4 hR0 t ht
  have hdM : DifferentiableOn ℝ (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2)
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hM' t ht).differentiableAt).differentiableWithinAt
  have hdK : DifferentiableOn ℝ
      (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hK' t ht).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun s => (Real.log (∑' n, (catalan n : ℝ) * s ^ n)) ^ 2))
      (deriv (fun s => ∑' n, (harmD n / ((n : ℝ) + 1)) * s ^ (n + 1)))
      (Metric.ball (0 : ℝ) R) := by
    intro t ht
    rw [(hM' t ht).deriv, (hK' t ht).deriv, hMD t ht]
  have h0 : (Real.log (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n)) ^ 2
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1) := by
    rw [S_tsum_zero, Real.log_one, K_tsum_zero]
    norm_num
  have heq := IsOpen.eqOn_of_deriv_eq hopen hconn hdM hdK hderiv hy0 h0
  exact heq hy

/-- The identity holds with `HasSum` for `|x| < 1 / 4`. -/
theorem interior_HasSum (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  set R : ℝ := max ((|x| + 1 / 4) / 2) (1 / 8) with hRdef
  have hR1 : |x| < R := by
    rw [hRdef]
    exact lt_of_lt_of_le (by linarith [hx]) (le_max_left _ _)
  have hR4 : R < 1 / 4 := by
    rw [hRdef]
    exact max_lt_iff.mpr ⟨by linarith [hx], by norm_num⟩
  have hR8 : 1 / 8 ≤ R := by
    rw [hRdef]
    exact le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR8
  have hy : x ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact hR1
  have hMK := M_eq_K R hR4 hR0 hR8 x hy
  have hKsumm : Summable (fun n => (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
      ((summable_dnorm x hx).mul_right (1 / 4 : ℝ))
    intro n
    have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    have e : (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1)
        = (harmD n * x ^ n) * (x / ((n : ℝ) + 1)) := by ring
    rw [e, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hNpos.le]
    calc |x| / ((n : ℝ) + 1) ≤ (1 / 4) / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_right (le_of_lt hx) hNpos.le
      _ ≤ 1 / 4 := div_le_self (by norm_num) hN1
  have hfun : (fun n => (harmD n / ((n : ℝ) + 1)) * x ^ (n + 1))
      = (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    simp only [harmD, harmDiff, Nat.centralBinom_eq_two_mul_choose]
    ring
  rw [← hfun, hMK]
  exact hKsumm.hasSum

/-- Sharp central-binomial bound from the recurrence ratio. -/
theorem cb_sqrt_bound (n : ℕ) : (Nat.centralBinom n : ℝ) ≤ 4 ^ n / √(3 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ihn =>
    have hcb := cb_succ_real n
    have hpos1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hpos1
    have hsq1 : (0 : ℝ) < √(3 * (n : ℝ) + 1) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hsq4 : (0 : ℝ) < √(3 * (n : ℝ) + 4) := by
      apply Real.sqrt_pos.mpr
      positivity
    have hneS1 : √(3 * (n : ℝ) + 1) ≠ 0 := ne_of_gt hsq1
    have hneS4 : √(3 * (n : ℝ) + 4) ≠ 0 := ne_of_gt hsq4
    have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hsq : (2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4)
        ≤ (2 * ((n : ℝ) + 1)) ^ 2 * (3 * (n : ℝ) + 1) := by
      have e : (2 * ((n : ℝ) + 1)) ^ 2 * (3 * (n : ℝ) + 1)
            - ((2 * (n : ℝ) + 1) ^ 2 * (3 * (n : ℝ) + 4)) = (n : ℝ) := by ring
      linarith [e, hnn]
    have hA : (0 : ℝ) ≤ 2 * (n : ℝ) + 1 := by positivity
    have hB : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by positivity
    have h1 : (2 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4)
        ≤ 2 * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      have hs := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB] at hs
      exact hs
    have hPnn : (0 : ℝ) ≤ 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) := by positivity
    have hstep : (Nat.centralBinom (n + 1) : ℝ)
        ≤ 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)) := by
      rw [hcb]
      exact mul_le_mul_of_nonneg_left ihn hPnn
    have hMpos : (0 : ℝ) < ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4) := by
      positivity
    have e : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)))
          * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
        = 2 * (2 * (n : ℝ) + 1) * 4 ^ n * √(3 * (n : ℝ) + 4) := by
      field_simp
    have e2 : (4 ^ (n + 1) / √(3 * (n : ℝ) + 4))
          * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
        = 4 ^ (n + 1) * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      field_simp
    have hle : 2 * (2 * (n : ℝ) + 1) * 4 ^ n * √(3 * (n : ℝ) + 4)
        ≤ 4 ^ (n + 1) * ((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) := by
      have hmul := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ 2 * 4 ^ n by positivity)
      have eP : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
      rw [eP]
      linarith [hmul]
    have hfin : 2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1))
        ≤ 4 ^ (n + 1) / √(3 * (n : ℝ) + 4) := by
      have hprod : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * (4 ^ n / √(3 * (n : ℝ) + 1)))
            * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4))
          ≤ (4 ^ (n + 1) / √(3 * (n : ℝ) + 4))
            * (((n : ℝ) + 1) * √(3 * (n : ℝ) + 1) * √(3 * (n : ℝ) + 4)) := by
        rw [e, e2]
        exact hle
      exact le_of_mul_le_mul_right hprod hMpos
    have eS : (3 * ((((n + 1 : ℕ))) : ℝ) + 1) = 3 * (n : ℝ) + 4 := by push_cast; ring
    rw [eS]
    exact le_trans hstep hfin

/-- Splitting off the square root from a 3/2 power. -/
theorem rpow_le_mul_sqrt (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    a ^ (3 / 2 : ℝ) ≤ a * √b := by
  have e : a ^ (3 / 2 : ℝ) = a * √a := by
    have e32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [e32, Real.rpow_add ha, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [e]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) ha.le

theorem summable_rpow32 : Summable (fun n : ℕ => ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹)) := by
  have h : Summable (fun n : ℕ => (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have h2 := (summable_nat_add_iff 1).mpr h
  have heq : (fun n : ℕ => ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹))
      = (fun n : ℕ => (((((n + 1 : ℕ))) : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    funext n
    rw [Nat.cast_add, Nat.cast_one]
  rw [heq]
  exact h2

/-- Pointwise Catalan bound against the 3/2 series. -/
theorem cat_closed_bound (n : ℕ) :
    (catalan n : ℝ) * (1 / 4 : ℝ) ^ n ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hC := catalan_cast n
  have hcb := cb_sqrt_bound n
  have hx1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have h14 : (1 / 4 : ℝ) ^ n = 1 / (4 : ℝ) ^ n := by rw [div_pow, one_pow]
  have eCat : (catalan n : ℝ) * (1 / 4 : ℝ) ^ n
      = (Nat.centralBinom n : ℝ) / (((n : ℝ) + 1) * 4 ^ n) := by
    rw [hC, h14, div_mul_div_comm, mul_one]
  have hle1 : (Nat.centralBinom n : ℝ) / (((n : ℝ) + 1) * 4 ^ n)
      ≤ (4 ^ n / √(3 * (n : ℝ) + 1)) / (((n : ℝ) + 1) * 4 ^ n) :=
    div_le_div_of_nonneg_right hcb (by positivity)
  have e2 : (4 ^ n / √(3 * (n : ℝ) + 1)) / (((n : ℝ) + 1) * 4 ^ n)
      = (√(3 * (n : ℝ) + 1) * ((n : ℝ) + 1))⁻¹ := by
    have h1 : (4 : ℝ) ^ n ≠ 0 := by positivity
    have h2 : √(3 * (n : ℝ) + 1) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hx1
    field_simp
  have hrpow := rpow_le_mul_sqrt ((n : ℝ) + 1) (3 * (n : ℝ) + 1) hx1 (by linarith [hnn])
  have hposR : (0 : ℝ) < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx1 _
  have hposS : (0 : ℝ) < √(3 * (n : ℝ) + 1) * ((n : ℝ) + 1) := by positivity
  have hle2 : (√(3 * (n : ℝ) + 1) * ((n : ℝ) + 1))⁻¹ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [inv_le_inv₀ hposS hposR, mul_comm]
    exact hrpow
  rw [eCat]
  exact le_trans hle1 (by rw [e2]; exact hle2)

/-- The harmonic difference is at most one. -/
theorem harmDiff_le_one (n : ℕ) : harmDiff n ≤ 1 := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (2 * (n + 1) - 1) := by
    intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  have hsplit : harmDiff n
      = ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹ := by
    simp only [harmDiff]
    rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hcard : (Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1)).card = n := by
    have hinter : Finset.range (n + 1) ∩ Finset.range (2 * (n + 1) - 1)
        = Finset.range (n + 1) := by
      ext k
      simp only [Finset.mem_inter, Finset.mem_range]
      omega
    rw [Finset.card_sdiff, hinter, Finset.card_range, Finset.card_range]
    omega
  have h1 : ∀ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1),
      ((k : ℝ) + 1)⁻¹ ≤ 1 / ((n : ℝ) + 2) := by
    intro k hk
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hk
    have hkn : n + 1 ≤ k := by omega
    have hcast : ((n : ℝ) + 2) ≤ ((k : ℝ) + 1) := by
      have hc : (((n + 1 : ℕ)) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkn
      push_cast at hc
      linarith [hc]
    have hpos1 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hpos2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [one_div]
    exact (inv_le_inv₀ hpos2 hpos1).mpr hcast
  rw [hsplit]
  calc ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹
      ≤ ∑ k ∈ Finset.range (2 * (n + 1) - 1) \ Finset.range (n + 1), (1 / ((n : ℝ) + 2)) :=
        Finset.sum_le_sum h1
    _ = (n : ℝ) * (1 / ((n : ℝ) + 2)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        linarith [hnn]

/-- Pointwise log-squared coefficient bound against the 3/2 series. -/
theorem Kterm_closed_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ‖(Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      harmDiff n * t ^ (n + 1) / ((n : ℝ) + 1)‖
      ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  have hcb := cb_sqrt_bound (n + 1)
  have hΔ := harmDiff_nonneg n
  have hΔ1 := harmDiff_le_one n
  have hcbnn : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) := by positivity
  have hx1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have ht4 : |t| ^ (n + 1) ≤ (1 / 4 : ℝ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg t) ht (n + 1)
  have hCnn : (0 : ℝ) ≤ 4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by
    apply div_nonneg (by positivity) (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg hcbnn, abs_of_nonneg hΔ, abs_of_nonneg hx1.le]
  have s1 : (Nat.centralBinom (n + 1) : ℝ) * harmDiff n
      ≤ 4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by
    have hmul := mul_le_mul hcb hΔ1 hΔ hCnn
    simpa using hmul
  have s2 : (Nat.centralBinom (n + 1) : ℝ) * harmDiff n * |t| ^ (n + 1)
      ≤ (4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1) :=
    mul_le_mul s1 ht4 (pow_nonneg (abs_nonneg t) _) hCnn
  have eM : ((4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1))
        / ((n : ℝ) + 1)
      = ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹) := by
    have h14 : (1 / 4 : ℝ) ^ (n + 1) = 1 / (4 : ℝ) ^ (n + 1) := by rw [div_pow, one_pow]
    rw [h14]
    have h1 : (4 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    have h2 : √(3 * (((n + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      positivity
    have h3 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hx1
    field_simp
  have hrpow := rpow_le_mul_sqrt ((n : ℝ) + 1) (3 * (((n + 1 : ℕ)) : ℝ) + 1) hx1 (by
    have ecast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [ecast]
    linarith [hnn])
  have hposR : (0 : ℝ) < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx1 _
  have hposS : (0 : ℝ) < ((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1) := by positivity
  have eR : ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹)
      ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    rw [inv_le_inv₀ hposS hposR]
    exact hrpow
  calc (Nat.centralBinom (n + 1) : ℝ) * harmDiff n * |t| ^ (n + 1) / ((n : ℝ) + 1)
      ≤ ((4 ^ (n + 1) / √(3 * (((n + 1 : ℕ)) : ℝ) + 1)) * (1 / 4 : ℝ) ^ (n + 1))
        / ((n : ℝ) + 1) :=
        div_le_div_of_nonneg_right s2 hx1.le
    _ = ((((n : ℝ) + 1) * √(3 * (((n + 1 : ℕ)) : ℝ) + 1))⁻¹) := eM
    _ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := eR

theorem Scat_closed_bound (n : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 4) :
    ‖(catalan n : ℝ) * t ^ n‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  have hnn : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn]
  have ht4 : |t| ^ n ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg t) ht n
  have s1 : (catalan n : ℝ) * |t| ^ n ≤ (catalan n : ℝ) * (1 / 4 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_left ht4 hnn
  exact le_trans s1 (cat_closed_bound n)

theorem summable_cat_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Summable (fun n => ‖(catalan n : ℝ) * t ^ n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
  intro n
  exact Scat_closed_bound n t ht

theorem harmD_target_eq (n : ℕ) (t : ℝ) :
    (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)
      = (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) * harmDiff n * t ^ (n + 1) / ((n : ℝ) + 1) := by
  simp only [harmD, Nat.centralBinom_eq_two_mul_choose]
  ring

theorem summable_Kharm_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    Summable (fun n => ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
  intro n
  rw [harmD_target_eq n t]
  exact Kterm_closed_bound n t ht

/-- The Catalan generating function is positive on the closed disc. -/
theorem S_pos_closed (t : ℝ) (ht : |t| ≤ 1 / 4) :
    0 < ∑' n, (catalan n : ℝ) * t ^ n := by
  have hsum : Summable (fun n => (catalan n : ℝ) * t ^ n) :=
    (summable_cat_closed t ht).of_norm
  have hE : ∀ K, (1 : ℝ) + t ≤ ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * t ^ n := by
    intro K
    induction K with
    | zero =>
      have e0 : 2 * (0 + 1) = 2 := by norm_num
      rw [e0]
      have h2 : ∑ n ∈ Finset.range 2, (catalan n : ℝ) * t ^ n = 1 + t := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [catalan_zero, catalan_one]
      rw [h2]
    | succ K ih =>
      have hstep : ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * t ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K + 1 + 1)), (catalan n : ℝ) * t ^ n := by
        have e : 2 * (K + 1 + 1) = 2 * (K + 1) + 1 + 1 := by omega
        rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp := pair_nonneg t ht (K + 1)
        linarith [hp]
      exact le_trans ih hstep
  have hPr : ∀ N, 2 ≤ N → 1 + t ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n := by
    intro N hN
    rcases Nat.even_or_odd N with hE' | hO
    · obtain ⟨K, rfl⟩ := hE'
      have hK : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h := hE K'
      have e : K' + 1 + (K' + 1) = 2 * (K' + 1) := by omega
      rw [e]
      exact h
    · obtain ⟨K, rfl⟩ := hO
      have hK1 : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h1 : ∑ n ∈ Finset.range (2 * (K' + 1)), (catalan n : ℝ) * t ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K' + 1) + 1), (catalan n : ℝ) * t ^ n := by
        rw [Finset.sum_range_succ]
        have hnn : (0 : ℝ) ≤ (catalan (2 * (K' + 1)) : ℝ) * t ^ (2 * (K' + 1)) := by
          apply mul_nonneg (by positivity)
          have e : t ^ (2 * (K' + 1)) = (t ^ (K' + 1)) ^ 2 := by ring
          rw [e]
          exact sq_nonneg _
        linarith [hnn]
      have h2 := hE K'
      linarith [h1, h2]
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n) Filter.atTop
      (nhds (∑' n, (catalan n : ℝ) * t ^ n)) :=
    (Summable.hasSum_iff_tendsto_nat hsum).mp hsum.hasSum
  have hev : ∀ᶠ N in Filter.atTop, (1 : ℝ) + t ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * t ^ n :=
    Filter.eventually_atTop.mpr ⟨2, fun N hN => hPr N hN⟩
  have hge := ge_of_tendsto hlim hev
  have ht34 : (3 / 4 : ℝ) ≤ 1 + t := by
    have hab : -|t| ≤ t := neg_abs_le t
    linarith [ht, hab]
  linarith [hge, ht34]

theorem continuousOn_S_closed :
    ContinuousOn (fun t => ∑' n, (catalan n : ℝ) * t ^ n)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
  have hf : ∀ n : ℕ, ContinuousOn (fun t => (catalan n : ℝ) * t ^ n)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro n
    exact ((continuous_const.mul (continuous_id.pow n)).continuousOn)
  have hfu : ∀ n : ℕ, ∀ t : ℝ, t ∈ Metric.closedBall 0 (1 / 4 : ℝ) →
      ‖(catalan n : ℝ) * t ^ n‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    exact Scat_closed_bound n t hmem
  exact continuousOn_tsum hf summable_rpow32 hfu

theorem continuousOn_Kharm_closed :
    ContinuousOn (fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
  have hf : ∀ n : ℕ, ContinuousOn (fun t => (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro n
    exact ((continuous_const.mul (continuous_id.pow (n + 1))).continuousOn)
  have hfu : ∀ n : ℕ, ∀ t : ℝ, t ∈ Metric.closedBall 0 (1 / 4 : ℝ) →
      ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖ ≤ ((((n : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    change ‖(harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)‖ ≤ _
    rw [harmD_target_eq n t]
    exact Kterm_closed_bound n t hmem
  exact continuousOn_tsum hf summable_rpow32 hfu

/-- Interior value identity in product form. -/
theorem F_eq_G_interior (t : ℝ) (ht : |t| < 1 / 4) :
    (∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      = (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n)) := by
  set R : ℝ := max ((|t| + 1 / 4) / 2) (1 / 8) with hRdef
  have hR1 : |t| < R := by
    rw [hRdef]
    exact lt_of_lt_of_le (by linarith [ht]) (le_max_left _ _)
  have hR4 : R < 1 / 4 := by
    rw [hRdef]
    exact max_lt_iff.mpr ⟨by linarith [ht], by norm_num⟩
  have hR8 : 1 / 8 ≤ R := by
    rw [hRdef]
    exact le_max_right _ _
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR8
  have hy : t ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    exact hR1
  have hMK := M_eq_K R hR4 hR0 hR8 t hy
  rw [← hMK, pow_two]

/-- The identity holds with `HasSum` on the boundary `|x| = 1 / 4`. -/
theorem boundary_HasSum (x₀ : ℝ) (hx₀ : |x₀| = 1 / 4) :
    HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x₀ ^ n)) ^ 2) := by
  have hSne : ∀ t ∈ Metric.closedBall (0 : ℝ) (1 / 4 : ℝ),
      (∑' n, (catalan n : ℝ) * t ^ n) ≠ 0 := by
    intro t ht
    have hmem : |t| ≤ 1 / 4 := by
      have h := Metric.mem_closedBall.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    exact ne_of_gt (S_pos_closed t hmem)
  have hG_closed : ContinuousOn
      (fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n)))
      (Metric.closedBall 0 (1 / 4 : ℝ)) :=
    (continuousOn_S_closed.log hSne).mul (continuousOn_S_closed.log hSne)
  have hu : ContinuousOn (fun s : ℝ => s * x₀) (Set.Icc 0 1) :=
    (continuous_id.mul_const x₀).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ => s * x₀) (Set.Icc 0 1)
      (Metric.closedBall 0 (1 / 4 : ℝ)) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    have hmem : |(s * x₀)| ≤ 1 / 4 := by
      rw [abs_mul, hx₀, abs_of_nonneg hs.1]
      linarith [hs.2]
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    exact hmem
  have hFcomp : ContinuousOn
      ((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
      (Set.Icc 0 1) :=
    continuousOn_Kharm_closed.comp hu hmaps
  have hGcomp : ContinuousOn
      ((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
      (Set.Icc 0 1) :=
    hG_closed.comp hu hmaps
  have hsn_mem : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ Set.Icc 0 1 := by
    intro n
    rw [Set.mem_Icc]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]
      have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith [hnn]
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := le_of_lt (by positivity)
    constructor <;> linarith [h0, h1]
  have hsn_lt : ∀ n : ℕ, (1 : ℝ) - 1 / ((n : ℝ) + 1) < 1 := by
    intro n
    have h0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [h0]
  have hseq1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) Filter.atTop
      (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hseqIcc : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) - 1 / ((n : ℝ) + 1) ∈ Set.Icc 0 1 :=
    Filter.Eventually.of_forall hsn_mem
  have hseqW :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq1 hseqIcc
  have hmem1 : (1 : ℝ) ∈ Set.Icc 0 1 := Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩
  have hlimF : Filter.Tendsto
      (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      Filter.atTop
      (nhds (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
        ∘ fun s : ℝ => s * x₀) 1)) :=
    Filter.Tendsto.comp (hFcomp.continuousWithinAt hmem1) hseqW
  have hlimG : Filter.Tendsto
      (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      Filter.atTop
      (nhds (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀) 1)) :=
    Filter.Tendsto.comp (hGcomp.continuousWithinAt hmem1) hseqW
  have heq_fg : Filter.EventuallyEq Filter.atTop
      (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1)) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
      (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀)
        ∘ fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) := by
    apply Filter.Eventually.of_forall
    intro n
    simp only [Function.comp_apply]
    have habs : |(1 - 1 / ((n : ℝ) + 1)) * x₀| < 1 / 4 := by
      rw [abs_mul, hx₀]
      have hs0 := (Set.mem_Icc.mp (hsn_mem n)).1
      have hs1 := hsn_lt n
      rw [abs_of_nonneg hs0]
      linarith [hs0, hs1]
    exact F_eq_G_interior _ habs
  have hval : (((fun t => ∑' n, (harmD n / ((n : ℝ) + 1)) * t ^ (n + 1))
      ∘ fun s : ℝ => s * x₀) 1)
      = (((fun t => (Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * t ^ n))) ∘ fun s : ℝ => s * x₀) 1) :=
    tendsto_nhds_unique_of_eventuallyEq hlimF hlimG heq_fg
  have hvalTS : (∑' n, (harmD n / ((n : ℝ) + 1)) * x₀ ^ (n + 1))
      = (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n)) := by
    simpa [Function.comp_apply] using hval
  have hKt : Summable (fun n => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      harmDiff n * x₀ ^ (n + 1) / ((n : ℝ) + 1)) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ summable_rpow32
    intro n
    exact Kterm_closed_bound n x₀ (le_of_eq hx₀)
  have htsum_eq2 : (∑' n, (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      = ∑' n, (harmD n / ((n : ℝ) + 1)) * x₀ ^ (n + 1) := by
    apply tsum_congr
    intro n
    simp only [harmD, harmDiff, Nat.centralBinom_eq_two_mul_choose]
    ring
  have hfun : (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        harmDiff n * x₀ ^ (n + 1) / ((n : ℝ) + 1))
      = (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1)) := by
    funext n
    simp only [harmDiff]
  have hHas : HasSum
      (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x₀ ^ (n + 1) / ((n : ℝ) + 1))
      ((Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))
        * (Real.log (∑' n, (catalan n : ℝ) * x₀ ^ n))) := by
    have h1 := hKt.hasSum
    rw [hfun, htsum_eq2, hvalTS] at h1
    exact h1
  rw [pow_two]
  exact hHas

/-- The source-level reciprocal sum is the real cast of `harmonic`. -/
theorem sum_inv_eq_harmonic_cast (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k : ℝ) + 1)⁻¹) = ((harmonic m : ℚ) : ℝ) := by
  induction m with
  | zero => simp [harmonic_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, harmonic_succ, ih, Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast]
    congr 1
    push_cast
    ring

/-- The canonical summand agrees with the source-level summand. -/
theorem canonical_term_eq_source (n : ℕ) (x : ℝ) :
    (Nat.centralBinom (n + 1) : ℝ) *
        (((harmonic (2 * (n + 1) - 1) : ℚ) : ℝ) - ((harmonic (n + 1) : ℚ) : ℝ)) *
        x ^ (n + 1) / ((n : ℝ) + 1)
      = (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
        ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
          (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
        x ^ (n + 1) / ((n : ℝ) + 1) := by
  rw [Nat.centralBinom_eq_two_mul_choose,
    ← sum_inv_eq_harmonic_cast (2 * (n + 1) - 1),
    ← sum_inv_eq_harmonic_cast (n + 1)]

/--
Knuth's identity for central binomial coefficients and harmonic numbers, stated with the
standard `Nat.centralBinom` and `harmonic` APIs.
This is the canonical form of `knuth_catalan_log_sq` below.
-/
theorem knuth_catalan_log_sq_canonical (x : ℝ) (hx : |x| ≤ 1 / 4) :
  HasSum
    (fun n : ℕ => (Nat.centralBinom (n + 1) : ℝ) *
      (((harmonic (2 * (n + 1) - 1) : ℚ) : ℝ) - ((harmonic (n + 1) : ℚ) : ℝ)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact (interior_HasSum x hlt).congr_fun (fun n => canonical_term_eq_source n x)
  · exact (boundary_HasSum x heq).congr_fun (fun n => canonical_term_eq_source n x)

/--
Knuth's identity for central binomial coefficients and harmonic numbers.

Source: Hongwei Chen, "Interesting Series Associated with Central Binomial Coefficients, Catalan
Numbers and Harmonic Numbers", Journal of Integer Sequences 19 (2016), Article 16.1.5, Theorem
`eq:k_gf`, lines 229-234, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Chen/chen21.tex>.

Proves `Wanted` entry `knuth_catalan_log_sq`.
-/
theorem knuth_catalan_log_sq (x : ℝ) (hx : |x| ≤ 1 / 4) :
  HasSum
    (fun n : ℕ => (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) *
      ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹) -
        (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) *
      x ^ (n + 1) / ((n : ℝ) + 1))
    ((Real.log (∑' n : ℕ, (catalan n : ℝ) * x ^ n)) ^ 2) := by
  exact (knuth_catalan_log_sq_canonical x hx).congr_fun
    (fun n => (canonical_term_eq_source n x).symm)

end MetaMathlibExt
end

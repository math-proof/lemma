import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma l1_norm_coeff_le [NontriviallyNormedField L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (n : ℕ) : ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n := by
  apply (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)
private lemma l1_norm_term_le [NontriviallyNormedField L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (_ : ‖a‖ < ρ) (j m : ℕ) : ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := by
  rw [norm_mul, norm_pow, div_pow]
  have h1 := l1_norm_coeff_le F hρ hF (j + m)
  rw [pow_add] at h1
  calc
    _ ≤ M / (ρ ^ j * ρ ^ m) * ‖a‖ ^ m := by gcongr
    _ = M / ρ ^ j * (‖a‖ ^ m / ρ ^ m) := by ring
    _ = M / ρ ^ j * (‖a‖ / ρ) ^ m := by
      rw [div_pow]
      ring
private lemma l1_norm_shift_term_le [NontriviallyNormedField L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (n k : ℕ) : ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := by
  have h := l1_norm_term_le F hρ hF a ha n k
  rw [norm_mul, norm_mul]
  rw [norm_mul] at h
  have hc : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc
    _ ≤ ‖PowerSeries.coeff (n + k) F‖ * 1 * ‖a ^ k‖ := by gcongr
    _ = ‖PowerSeries.coeff (n + k) F‖ * ‖a ^ k‖ := by rw [mul_one]
    _ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := h
private lemma l1_tsum_prod_eq_tsum_sum_antidiagonal [NontriviallyNormedField L] [CompleteSpace L] (T : ℕ × ℕ → L) (hT : Summable T) : ∑' p : ℕ × ℕ, T p = ∑' N : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, T p := by
  have h1 : Summable (fun c : (Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n) => T (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd c)) := (Equiv.summable_iff _).mpr hT
  rw [← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd).tsum_eq T, h1.tsum_sigma' (fun N => (hasSum_fintype _).summable)]
  refine tsum_congr fun N => ?_
  rw [← Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal N) T]
  rfl
/--
[PowerSeries_tsum_coeff_taylorShift_mul_pow_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_tsum_coeff_taylorShift_mul_pow_eq.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
  (a : L) (ha : ‖a‖ < ρ) (b : L) (hb : ‖b‖ < ρ) :
  -- imply
  ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n = ∑' n, PowerSeries.coeff n F * (a + b) ^ n := by
  -- proof
  set T : ℕ × ℕ → L := fun p => PowerSeries.coeff (p.1 + p.2) F * ((p.1 + p.2).choose p.1 : L) * a ^ p.2 * b ^ p.1 with hT
  have hra : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hra0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hrb : ‖b‖ / ρ < 1 := (div_lt_one hρ).mpr hb
  have hrb0 : 0 ≤ ‖b‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hdom : ∀ p : ℕ × ℕ, ‖T p‖ ≤ M * ((‖b‖ / ρ) ^ p.1 * (‖a‖ / ρ) ^ p.2) := by
    rintro ⟨n, k⟩
    rw [hT]
    rw [norm_mul, norm_pow]
    have h1 := l1_norm_shift_term_le F hρ hF a ha n k
    calc
      _ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k * ‖b‖ ^ n := by gcongr
      _ = M * ((‖b‖ / ρ) ^ n * (‖a‖ / ρ) ^ k) := by
        rw [div_pow, div_pow]
        ring
  have hsum : Summable T := by
    refine Summable.of_norm_bounded ?_ hdom
    apply ((summable_geometric_of_lt_one hrb0 hrb).mul_of_nonneg (summable_geometric_of_lt_one hra0 hra) (fun _ => pow_nonneg hrb0 _) (fun _ => pow_nonneg hra0 _)).mul_left M
  have hLHS : ∑' n, PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) * b ^ n = ∑' p : ℕ × ℕ, T p := by
    rw [hsum.tsum_prod' (fun n => hsum.prod_factor n)]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_mk, ← tsum_mul_right]
  have hRHS : ∑' N, PowerSeries.coeff N F * (a + b) ^ N = ∑' p : ℕ × ℕ, T p := by
    rw [l1_tsum_prod_eq_tsum_sum_antidiagonal T hsum]
    refine tsum_congr fun N => ?_
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_comm a b, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    simp only [hT, Prod.fst_mk, Prod.snd_mk]
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ hm)]
    ring
  rw [hLHS, hRHS]


-- created on 2026-10-20

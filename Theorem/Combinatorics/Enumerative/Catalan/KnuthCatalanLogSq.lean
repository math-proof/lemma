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


section

open scoped BigOperators

namespace MetaMathlibExt

/-! # Knuth Catalan log-squared generating function -/

theorem cb_succ_real (m : ℕ) :
    (Nat.centralBinom (m + 1) : ℝ) = 2 * (2 * (m : ℝ) + 1) / ((m : ℝ) + 1) *
      (Nat.centralBinom m : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have hcast : ((m : ℝ) + 1) * (Nat.centralBinom (m + 1) : ℝ)
      = 2 * (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ) := by
    exact_mod_cast h
  have hne : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hcast]

theorem catalan_cast (n : ℕ) :
    (catalan n : ℝ) = (Nat.centralBinom n : ℝ) / ((n : ℝ) + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hcast : ((n : ℝ) + 1) * (catalan n : ℝ) = (Nat.centralBinom n : ℝ) := by
    exact_mod_cast h
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  linarith [hcast]

theorem cat_le_four_pow (n : ℕ) : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by
  have h := Nat.centralBinom_le_four_pow n
  have h2 := succ_mul_catalan_eq_centralBinom n
  rw [← h2] at h
  have h3 : catalan n ≤ 4 ^ n := by
    calc catalan n = 1 * catalan n := by rw [one_mul]
      _ ≤ (n + 1) * catalan n := by
        gcongr
        omega
      _ ≤ 4 ^ n := h
  exact_mod_cast h3

theorem catalan_succ_eq (n : ℕ) : (catalan (n + 1) : ℝ)
    = (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2)) * (catalan n : ℝ) := by
  have e1 := catalan_cast (n + 1)
  have e2 := catalan_cast n
  have eN : ((((n + 1 : ℕ))) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have h2 : (Nat.centralBinom (n + 1) : ℝ)
      = (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) * (Nat.centralBinom n : ℝ) :=
    cb_succ_real n
  have hne1 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hne2 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [e1, e2, eN, h2]
  field_simp

theorem catalan_succ_le (n : ℕ) : (catalan (n + 1) : ℝ) ≤ 4 * (catalan n : ℝ) := by
  rw [catalan_succ_eq]
  have hnn : (0 : ℝ) ≤ catalan n := by positivity
  have hfac : (2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2)) ≤ 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_mul_of_nonneg_right hfac hnn

theorem summable_cat_norm (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n => ‖(catalan n : ℝ) * x ^ n‖) := by
  have hq : (4 : ℝ) * |x| < 1 := by linarith [hx]
  have hnn : (0 : ℝ) ≤ 4 * |x| := by positivity
  have hgeom := summable_geometric_of_lt_one hnn hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hgeom
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (catalan n : ℝ))]
  calc (catalan n : ℝ) * |x| ^ n
      ≤ (4 : ℝ) ^ n * |x| ^ n :=
        mul_le_mul_of_nonneg_right (cat_le_four_pow n) (pow_nonneg (abs_nonneg x) n)
    _ = (4 * |x|) ^ n := by ring

theorem summable_cat (x : ℝ) (hx : |x| < 1 / 4) :
    Summable (fun n => (catalan n : ℝ) * x ^ n) :=
  (summable_cat_norm x hx).of_norm

/-- Each consecutive pair of terms is nonnegative inside the closed radius. -/
theorem pair_nonneg (x : ℝ) (hx : |x| ≤ 1 / 4) (k : ℕ) :
    (0 : ℝ) ≤ (catalan (2 * k) : ℝ) * x ^ (2 * k)
      + (catalan (2 * k + 1) : ℝ) * x ^ (2 * k + 1) := by
  have h4 : 4 * |x| ≤ 1 := by linarith [hx]
  have hle : (catalan (2 * k + 1) : ℝ) ≤ 4 * (catalan (2 * k) : ℝ) := by
    have h := catalan_succ_le (2 * k)
    rwa [show 2 * k + 1 = (2 * k) + 1 from rfl] at h
  have hnn : (0 : ℝ) ≤ (catalan (2 * k) : ℝ) := by positivity
  have hnn1 : (0 : ℝ) ≤ (catalan (2 * k + 1) : ℝ) := by positivity
  have hsq : (0 : ℝ) ≤ x ^ (2 * k) := by
    have e : x ^ (2 * k) = (x ^ k) ^ 2 := by ring
    rw [e]
    exact sq_nonneg _
  have hfactor : (catalan (2 * k) : ℝ) * x ^ (2 * k)
        + (catalan (2 * k + 1) : ℝ) * x ^ (2 * k + 1)
      = x ^ (2 * k) * ((catalan (2 * k) : ℝ) + (catalan (2 * k + 1) : ℝ) * x) := by
    ring
  rw [hfactor]
  apply mul_nonneg hsq
  have h1 : (catalan (2 * k + 1) : ℝ) * x ≥ -((catalan (2 * k + 1) : ℝ) * |x|) := by
    calc (catalan (2 * k + 1) : ℝ) * x
        ≥ (catalan (2 * k + 1) : ℝ) * (-|x|) := by
          apply mul_le_mul_of_nonneg_left _ hnn1
          exact neg_abs_le x
      _ = -((catalan (2 * k + 1) : ℝ) * |x|) := by ring
  have h2 : (catalan (2 * k + 1) : ℝ) * |x| ≤ 4 * (catalan (2 * k) : ℝ) * |x| := by
    have h := mul_le_mul_of_nonneg_right hle (abs_nonneg x)
    linarith [h]
  have hside : (catalan (2 * k) : ℝ) + (catalan (2 * k + 1) : ℝ) * x
      ≥ (catalan (2 * k) : ℝ) * (1 - 4 * |x|) := by
    have h3 : (catalan (2 * k) : ℝ) * (1 - 4 * |x|)
        = (catalan (2 * k) : ℝ) - 4 * (catalan (2 * k) : ℝ) * |x| := by ring
    linarith [h1, h2, h3]
  have hpos : (0 : ℝ) ≤ (catalan (2 * k) : ℝ) * (1 - 4 * |x|) :=
    mul_nonneg hnn (by linarith [h4])
  linarith [hside, hpos]

/-- The Catalan generating function is positive inside the radius. -/
theorem catalan_tsum_pos (x : ℝ) (hx : |x| < 1 / 4) :
    0 < ∑' n, (catalan n : ℝ) * x ^ n := by
  have hsum := summable_cat x hx
  have hE : ∀ K, (1 : ℝ) + x ≤ ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * x ^ n := by
    intro K
    induction K with
    | zero =>
      have e0 : 2 * (0 + 1) = 2 := by norm_num
      rw [e0]
      have h2 : ∑ n ∈ Finset.range 2, (catalan n : ℝ) * x ^ n = 1 + x := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
        simp [catalan_zero, catalan_one]
      rw [h2]
    | succ K ih =>
      have hstep : ∑ n ∈ Finset.range (2 * (K + 1)), (catalan n : ℝ) * x ^ n
          ≤ ∑ n ∈ Finset.range (2 * (K + 1 + 1)), (catalan n : ℝ) * x ^ n := by
        have e : 2 * (K + 1 + 1) = 2 * (K + 1) + 1 + 1 := by omega
        rw [e, Finset.sum_range_succ, Finset.sum_range_succ]
        have hp := pair_nonneg x (le_of_lt hx) (K + 1)
        linarith [hp]
      exact le_trans ih hstep
  have hPr : ∀ N, 1 ≤ N → 1 - |x| ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n := by
    intro N hN
    have hx1 : (1 : ℝ) + x ≥ 1 - |x| := by linarith [neg_abs_le x]
    rcases Nat.even_or_odd N with hE | hO
    · obtain ⟨K, rfl⟩ := hE
      have eKK : K + K = 2 * K := by omega
      have hK : 1 ≤ K := by omega
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      have h := hE K'
      rw [show K' + 1 + (K' + 1) = 2 * (K' + 1) by omega]
      linarith [h, hx1]
    · obtain ⟨K, rfl⟩ := hO
      by_cases hK : K = 0
      · subst hK
        have e : 2 * 0 + 1 = 1 := by norm_num
        rw [e, Finset.sum_range_one]
        simp only [catalan_zero, Nat.cast_one, pow_zero, mul_one]
        linarith [abs_nonneg x]
      · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
        have h1 : ∑ n ∈ Finset.range (2 * K), (catalan n : ℝ) * x ^ n
            ≤ ∑ n ∈ Finset.range (2 * K + 1), (catalan n : ℝ) * x ^ n := by
          rw [Finset.sum_range_succ]
          have hnn : (0 : ℝ) ≤ (catalan (2 * K) : ℝ) * x ^ (2 * K) := by
            apply mul_nonneg (by positivity)
            have e : x ^ (2 * K) = (x ^ K) ^ 2 := by ring
            rw [e]
            exact sq_nonneg _
          linarith [hnn]
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        have h2 := hE K'
        linarith [h1, h2, hx1]
  have hlim : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n) Filter.atTop
      (nhds (∑' n, (catalan n : ℝ) * x ^ n)) :=
    (Summable.hasSum_iff_tendsto_nat hsum).mp hsum.hasSum
  have hev : ∀ᶠ N in Filter.atTop, (1 : ℝ) - |x| ≤ ∑ n ∈ Finset.range N, (catalan n : ℝ) * x ^ n :=
    Filter.eventually_atTop.mpr ⟨1, fun N hN => hPr N hN⟩
  have hge := ge_of_tendsto hlim hev
  have hrpos : (0 : ℝ) < 1 - |x| := by linarith [hx]
  linarith [hge, hrpos]

/-- Convolution of Catalan numbers with central binomial coefficients. -/
theorem conv_catalan_centralBinom (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ)
      = (Nat.centralBinom (n + 1) : ℝ) / 2 := by
  induction n with
  | zero =>
    have h1 : Nat.centralBinom 1 = 2 := by decide
    simp [Nat.centralBinom_zero, catalan_zero, h1]
  | succ n ih =>
    have hterm : ∀ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)
        = 4 * ((catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ))
          - 2 * ((catalan k : ℝ) * (catalan (n - k) : ℝ)) := by
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hcb := cb_succ_real (n - k)
      have hcat := catalan_cast (n - k)
      have hnk : n + 1 - k = (n - k) + 1 := by omega
      have hne : (((n - k : ℕ) : ℝ) + 1) ≠ 0 := by positivity
      rw [hnk, hcb, hcat]
      field_simp
      ring
    have hsum : ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)
        = 4 * (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (Nat.centralBinom (n - k) : ℝ))
          - 2 * (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    have hcat : ∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ)
        = (catalan (n + 1) : ℝ) := by
      have h := catalan_succ' n
      have h2 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => catalan a * catalan b) n
      have h3 : (∑ k ∈ Finset.range (n + 1), catalan k * catalan (n - k)) = catalan (n + 1) :=
        h2.symm.trans h.symm
      have hcast : (∑ k ∈ Finset.range (n + 1), (catalan k : ℝ) * (catalan (n - k) : ℝ))
          = (catalan (n + 1) : ℝ) := by exact_mod_cast h3
      exact hcast
    have hcb2 := cb_succ_real (n + 1)
    have hcat2 := catalan_cast (n + 1)
    have htop : n + 1 - (n + 1) = 0 := by omega
    rw [Finset.sum_range_succ, hsum, ih, hcat, htop,
      Nat.centralBinom_zero, Nat.cast_one, mul_one, hcb2, hcat2]
    have h1 : (((n + 1 : ℕ)) : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- Reflection symmetry of the Catalan-centralBinom convolution. -/
theorem conv_reflect (n : ℕ) :
    ∑ i ∈ Finset.range n, (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ)
      = ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - i) : ℝ) := by
  rw [← Finset.sum_range_reflect
    (fun i => (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ)) n]
  apply Finset.sum_congr rfl
  intro i hi
  have hi2 : i < n := Finset.mem_range.mp hi
  have e1 : n - 1 - i + 1 = n - i := by omega
  have e2 : n - (n - 1 - i) = i + 1 := by omega
  rw [e1, e2, mul_comm]

/-- Partial convolution with the top and bottom terms removed. -/
theorem conv_cb_catalan_part (n : ℕ) :
    ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - (i + 1) + 1) : ℝ)
      = (Nat.centralBinom (n + 1 + 1) : ℝ) / 2 - (Nat.centralBinom (n + 1) : ℝ)
        - (catalan (n + 1) : ℝ) := by
  have hI := conv_catalan_centralBinom (n + 1)
  rw [Finset.sum_range_succ', Finset.sum_range_succ] at hI
  have e0 : n + 1 - 0 = n + 1 := by omega
  have es : n + 1 - (n + 1) = 0 := by omega
  rw [e0, es, Nat.centralBinom_zero, catalan_zero] at hI
  simp only [Nat.cast_one, mul_one, one_mul] at hI
  have hmid : (∑ i ∈ Finset.range n,
      (catalan (i + 1) : ℝ) * (Nat.centralBinom (n + 1 - (i + 1)) : ℝ))
      = ∑ i ∈ Finset.range n, (catalan (i + 1) : ℝ) * (Nat.centralBinom (n - i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < n := Finset.mem_range.mp hi
    have e : n + 1 - (i + 1) = n - i := by omega
    rw [e]
  rw [hmid, conv_reflect] at hI
  have hB : (∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - i) : ℝ))
      = ∑ i ∈ Finset.range n, (Nat.centralBinom (i + 1) : ℝ) * (catalan (n - (i + 1) + 1) : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi2 : i < n := Finset.mem_range.mp hi
    have e : n - (i + 1) + 1 = n - i := by omega
    rw [e]
  rw [hB] at hI
  linarith [hI]

/-- Harmonic convolution identity: the coefficient identity behind the log-squared series. -/
theorem conv_cb_harmonic (n : ℕ) :
    ∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
        / (2 * ((m : ℝ) + 1))
      = (Nat.centralBinom (n + 1) : ℝ)
        * ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcb1 : Nat.centralBinom 1 = 2 := by decide
    -- top term of the peeled sum
    have htop : (Nat.centralBinom (n + 1) : ℝ) * (Nat.centralBinom (n + 1 - (n + 1) + 1) : ℝ)
          / (2 * ((n : ℝ) + 1))
        = (Nat.centralBinom (n + 1) : ℝ) / ((n : ℝ) + 1) := by
      have etop : n + 1 - (n + 1) + 1 = 1 := by omega
      rw [etop, hcb1]
      have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    -- per-term recurrence for the remaining sum
    have hterm : ∀ m ∈ Finset.range n,
        (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n + 1 - (m + 1) + 1) : ℝ)
          / (2 * ((m : ℝ) + 1))
        = 4 * ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (2 * ((m : ℝ) + 1)))
          - (Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1)) := by
      intro m hm
      have hm2 : m < n := Finset.mem_range.mp hm
      have e : n + 1 - (m + 1) + 1 = (n - (m + 1) + 1) + 1 := by omega
      have hcb := cb_succ_real (n - (m + 1) + 1)
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hj1 : ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
      rw [e, hcb]
      field_simp
      ring
    have hrest : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n + 1 - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)))
        = 4 * (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)))
          - (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl hterm
    -- partial fractions for the error sum
    have hEper : ∀ m ∈ Finset.range n,
        ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
        = (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
          + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ) := by
      intro m hm
      have hm2 : m < n := Finset.mem_range.mp hm
      have e : m + (n - (m + 1) + 1) + 2 = n + 2 := by omega
      have he : (m : ℝ) + ((((n - (m + 1) + 1 : ℕ)) : ℝ)) + 2 = (n : ℝ) + 2 := by
        exact_mod_cast e
      have hcat := catalan_cast (n - (m + 1) + 1)
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hj1 : ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
      have hform : ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
            - ((Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
              * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ))
          = ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
            * ((((n : ℝ) + 2) - ((m : ℝ) + 1) - ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) := by
        rw [hcat]
        field_simp
        ring
      have hside : ((n : ℝ) + 2) - ((m : ℝ) + 1) - ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1) = 0 := by
        linarith [he]
      have h0 : ((Nat.centralBinom (m + 1) : ℝ) * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
              / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
            - ((Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
              * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            + (Nat.centralBinom (m + 1) : ℝ) * (catalan (n - (m + 1) + 1) : ℝ)) = 0 := by
        rw [hform, hside, zero_div, mul_zero]
      exact eq_of_sub_eq_zero h0
    have hEmul : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1))) * ((n : ℝ) + 2)
        = (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
          + (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (catalan (n - (m + 1) + 1) : ℝ)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hEper
    have hE' : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ)
            / (((m : ℝ) + 1) * ((((n - (m + 1) + 1 : ℕ)) : ℝ) + 1)))
        = ((∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
          + (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (catalan (n - (m + 1) + 1) : ℝ))) / ((n : ℝ) + 2) := by
      have hN : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [eq_div_iff hN]
      exact hEmul
    have hA : (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ) / ((m : ℝ) + 1)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ))
        = 2 * (∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
            * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by
        have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hm2 : (2 : ℝ) * ((m : ℝ) + 1) ≠ 0 := by positivity
        field_simp)
    have hBval := conv_cb_catalan_part n
    -- harmonic number recurrence
    have hΔ : (∑ k ∈ Finset.range (2 * (n + 1 + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1 + 1), ((k : ℝ) + 1)⁻¹)
        = ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹))
          + (2 * (n : ℝ) + 2)⁻¹ + (2 * (n : ℝ) + 3)⁻¹ - ((n : ℝ) + 2)⁻¹ := by
      have eH1 : 2 * (n + 1 + 1) - 1 = 2 * (n + 1) - 1 + 1 + 1 := by omega
      rw [eH1, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      have f1 : ((((2 * (n + 1) - 1 + 1 : ℕ)) : ℝ) + 1)⁻¹ = (2 * (n : ℝ) + 3)⁻¹ := by
        have e : (2 * (n + 1) - 1 + 1 : ℕ) = 2 * n + 1 + 1 := by omega
        rw [e]
        have en : ((((2 * n + 1 + 1 : ℕ)) : ℝ) + 1) = 2 * (n : ℝ) + 3 := by push_cast; ring
        rw [en]
      have f2 : ((((2 * (n + 1) - 1 : ℕ)) : ℝ) + 1)⁻¹ = (2 * (n : ℝ) + 2)⁻¹ := by
        have e : (2 * (n + 1) - 1 : ℕ) = 2 * n + 1 := by omega
        rw [e]
        have en : ((((2 * n + 1 : ℕ)) : ℝ) + 1) = 2 * (n : ℝ) + 2 := by push_cast; ring
        rw [en]
      have g1 : ((((n + 1 : ℕ)) : ℝ) + 1)⁻¹ = ((n : ℝ) + 2)⁻¹ := by
        have en : ((((n + 1 : ℕ)) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
        rw [en]
      rw [f1, f2, g1]
      ring
    have hcb2 := cb_succ_real (n + 1)
    have hcat2 := catalan_cast (n + 1)
    conv_lhs => rw [Finset.sum_range_succ]
    rw [hrest, hE', hA, ih, hBval, htop, hΔ, hcb2, hcat2]
    push_cast
    have g1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have g2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have g2' : (((n : ℝ) + 1) + 1) ≠ 0 := by positivity
    have g3 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    have g4 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
    have g5 : ((((n + 1 : ℕ)) : ℝ) + 1) ≠ 0 := by positivity
    have g0 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp
    ring

/-- Coefficient identity for the derivative of the log series. -/
theorem conv_for_deriv (n : ℕ) :
    ((n : ℝ) + 1) * (catalan (n + 1) : ℝ)
      = ∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2) := by
  have hI := conv_catalan_centralBinom (n + 1)
  rw [Finset.sum_range_succ] at hI
  have etop : n + 1 - (n + 1) = 0 := by omega
  rw [etop, Nat.centralBinom_zero, Nat.cast_one, mul_one] at hI
  have h1 : (∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2))
      = (∑ k ∈ Finset.range (n + 1),
        (catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)) / 2 := by
    have h1a : (∑ k ∈ Finset.range (n + 1),
          (catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2))
        = ∑ k ∈ Finset.range (n + 1),
          (((catalan k : ℝ) * (Nat.centralBinom (n + 1 - k) : ℝ)) / 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      have e : n - k + 1 = n + 1 - k := by omega
      rw [e]
      ring
    rw [h1a, Finset.sum_div]
  have hcb2 := cb_succ_real (n + 1)
  have hcat2 := catalan_cast (n + 1)
  rw [h1]
  rw [hcb2] at hI
  rw [hcat2] at hI ⊢
  have hD : ((((n + 1 : ℕ))) : ℝ) + 1 ≠ 0 := by positivity
  push_cast at hI ⊢
  field_simp at hI ⊢
  linarith

/-- Coefficient identity for squaring the log series. -/
theorem conv_for_square (n : ℕ) :
    2 * (∑ k ∈ Finset.range (n + 1),
      ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ)) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)))
      = (Nat.centralBinom (n + 1) : ℝ)
        * ((∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
          - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)) := by
  have hC := conv_cb_harmonic n
  have hsplit : (∑ k ∈ Finset.range (n + 1),
        ((Nat.centralBinom k : ℝ) / (2 * (k : ℝ)) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)))
      = ∑ j ∈ Finset.range n,
        ((Nat.centralBinom (j + 1) : ℝ) / (2 * ((j : ℝ) + 1))
          * ((Nat.centralBinom (n - (j + 1) + 1) : ℝ) / 2)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.centralBinom_zero, Nat.cast_one, Nat.cast_zero, mul_zero, div_zero,
      zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.cast_add, Nat.cast_one]
  have h23 : 2 * (∑ j ∈ Finset.range n,
        ((Nat.centralBinom (j + 1) : ℝ) / (2 * ((j : ℝ) + 1))
          * ((Nat.centralBinom (n - (j + 1) + 1) : ℝ) / 2)))
      = ∑ m ∈ Finset.range n, (Nat.centralBinom (m + 1) : ℝ)
        * (Nat.centralBinom (n - (m + 1) + 1) : ℝ) / (2 * ((m : ℝ) + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hsplit, h23]
  exact hC

/-- Summable geometric majorant for power-series derivative bounds. -/
theorem majorant_summable (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 ≤ R) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5) := by
  have h4 : (4 : ℝ) * R < 1 := by linarith [hR4]
  have hnn : (0 : ℝ) ≤ 4 * R := by positivity
  have h4R : ‖(4 : ℝ) * R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h4
  have hW : Summable (fun n : ℕ => ((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n) := by
    have hgeom := (hasSum_choose_mul_geometric_of_norm_lt_one 1 h4R).summable
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n)
        = (fun n : ℕ => (((n + 1).choose 1 : ℕ) : ℝ) * ((4 : ℝ) * R) ^ n) := by
      funext n
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact hgeom
  have e : (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5)
      = (fun n : ℕ => (((n : ℝ) + 1) * ((4 : ℝ) * R) ^ n) * 20) := by
    funext n
    ring
  rw [e]
  exact hW.mul_right 20

/-- Termwise derivative of the Catalan generating function on a ball. -/
theorem S_hasDerivAt (x : ℝ) (_hx : |x| < 1 / 4) (R : ℝ) (_hR1 : |x| < R)
    (hR4 : R < 1 / 4) (hR8 : 1 / 8 ≤ R) (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => ∑' n, (catalan n : ℝ) * t ^ n)
      (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n) y := by
  have hR0 : 0 < R := by linarith [hR8]
  have hU : Summable (fun n : ℕ => ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5) :=
    majorant_summable R hR4 (le_of_lt hR0)
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hS0 : Summable (fun n => (catalan n : ℝ) * (0 : ℝ) ^ n) :=
    summable_cat 0 (by norm_num)
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖(catalan n : ℝ) * ((n : ℝ) * t ^ (n - 1))‖
        ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
    intro n t ht
    have e0 : (catalan n : ℝ) * ((n : ℝ) * t ^ (n - 1))
        = (catalan n : ℝ) * (n : ℝ) * t ^ (n - 1) := by ring
    rw [e0]
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hC : (catalan n : ℝ) ≤ 4 ^ n := cat_le_four_pow n
    have hnn : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
    by_cases hn : n = 0
    · subst hn
      simp only [catalan_zero, Nat.cast_zero, Nat.cast_one, zero_mul, mul_zero, norm_zero,
        pow_zero]
      positivity
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hpow : |t| ^ (n - 1) ≤ R ^ (n - 1) :=
        pow_le_pow_left₀ (abs_nonneg t) htb (n - 1)
      have hN : (n : ℝ) ≤ ((n : ℝ) + 1) * (20 * R) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n, hR8,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (by linarith [hR8] : (0 : ℝ) ≤ 20 * R - 1),
          hR0.le]
      have hnorm : ‖(catalan n : ℝ) * (n : ℝ) * t ^ (n - 1)‖
          = (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1) := by
        simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
      have step1 : (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1)
          ≤ (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1) := by
        have e1 : (catalan n : ℝ) * (n : ℝ) * |t| ^ (n - 1)
            = ((catalan n : ℝ) * |t| ^ (n - 1)) * (n : ℝ) := by ring
        have e2 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
            = ((4 : ℝ) ^ n * R ^ (n - 1)) * (n : ℝ) := by ring
        rw [e1, e2]
        apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (n : ℝ))
        apply mul_le_mul hC hpow (pow_nonneg (abs_nonneg t) _)
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _)
      have step2 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
          ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
        have eR : R ^ (n - 1) * R = R ^ n := by
          have e1 : n - 1 + 1 = n := by omega
          rw [← pow_succ, e1]
        have h1 : (n : ℝ) * ((4 : ℝ) ^ n * R ^ (n - 1))
            ≤ (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1)) :=
          mul_le_mul_of_nonneg_right hN
            (mul_nonneg (pow_nonneg (by norm_num) n) (pow_nonneg hR0.le _))
        have h2 : (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1))
            = ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by
          calc (((n : ℝ) + 1) * (20 * R)) * ((4 : ℝ) ^ n * R ^ (n - 1))
              = ((n : ℝ) + 1) * (4 : ℝ) ^ n * (R ^ (n - 1) * R) * 20 := by ring
            _ = ((n : ℝ) + 1) * (4 : ℝ) ^ n * (R ^ n) * 20 := by rw [eR]
            _ = ((n : ℝ) + 1) * (4 : ℝ) ^ (n + 1) * R ^ n * 5 := by ring
        have e3 : (4 : ℝ) ^ n * (n : ℝ) * R ^ (n - 1)
            = (n : ℝ) * ((4 : ℝ) ^ n * R ^ (n - 1)) := by ring
        rw [e3]
        linarith [h1, h2]
      rw [hnorm]
      linarith [step1, step2]
  have hmain : HasDerivAt (fun z => ∑' n, (catalan n : ℝ) * z ^ n)
      (∑' n, (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1))) y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => ((hasDerivAt_pow n t).const_mul (catalan n : ℝ)))
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hshift : (∑' n, (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1)))
      = ∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n := by
    have hFsumm : Summable (fun n => (catalan n : ℝ) * ((n : ℝ) * y ^ (n - 1))) := by
      apply Summable.of_norm
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hU
      intro n
      exact hbound n y hy
    rw [hFsumm.tsum_eq_zero_add]
    simp only [catalan_zero, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, zero_add]
    apply tsum_congr
    intro n
    have e : n + 1 - 1 = n := by omega
    have ecast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e, ecast]
    ring
  rw [hshift] at hmain
  exact hmain

theorem cb_le_four_pow_real (n : ℕ) : (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
  exact_mod_cast Nat.centralBinom_le_four_pow n

theorem summable_cbnorm (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => ‖(Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n‖) := by
  have hq : (4 : ℝ) * |y| < 1 := by linarith [hy]
  have hnn : (0 : ℝ) ≤ 4 * |y| := by positivity
  have hgeom := summable_geometric_of_lt_one hnn hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ (hgeom.mul_left 2)
  intro n
  have hC : (Nat.centralBinom (n + 1) : ℝ) ≤ 4 ^ (n + 1) := cb_le_four_pow_real _
  have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
  calc (Nat.centralBinom (n + 1) : ℝ) / 2 * |y| ^ n
      ≤ (4 ^ (n + 1) / 2) * |y| ^ n :=
        mul_le_mul_of_nonneg_right (by linarith [hC]) (pow_nonneg (abs_nonneg y) n)
    _ = 2 * (4 * |y|) ^ n := by ring

theorem summable_cb (y : ℝ) (hy : |y| < 1 / 4) :
    Summable (fun n => (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) :=
  (summable_cbnorm y hy).of_norm

theorem majorant_cb_summable (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 ≤ R) :
    Summable (fun n : ℕ => 2 * ((4 : ℝ) * R) ^ n) := by
  have h4 : (4 : ℝ) * R < 1 := by linarith [hR4]
  have hnn : (0 : ℝ) ≤ 4 * R := by positivity
  exact (summable_geometric_of_lt_one hnn h4).mul_left 2

/-- Termwise derivative of the integrated b-series on a ball. -/
theorem H_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt
      (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
      (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) y := by
  have hU := majorant_cb_summable R hR4 hR0.le
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hzero : (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
      = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  have hS0 : Summable
      (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1)) := by
    rw [hzero]
    exact summable_zero
  have hbound : ∀ n : ℕ, ∀ t ∈ Metric.ball (0 : ℝ) R,
      ‖((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)‖
        ≤ 2 * ((4 : ℝ) * R) ^ n := by
    intro n t ht
    have htb : |t| ≤ R := le_of_lt (by
      have h := Metric.mem_ball.mp ht
      rwa [dist_zero_right, Real.norm_eq_abs] at h)
    have hC : (Nat.centralBinom (n + 1) : ℝ) ≤ 4 ^ (n + 1) := cb_le_four_pow_real _
    have hnn2 : (0 : ℝ) ≤ (Nat.centralBinom (n + 1) : ℝ) / 2 := by positivity
    have hcancel : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
        = ((Nat.centralBinom (n + 1) : ℝ) / 2) * t ^ n := by
      have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    rw [hcancel, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hnn2]
    have hpow : |t| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg t) htb n
    calc (Nat.centralBinom (n + 1) : ℝ) / 2 * |t| ^ n
        ≤ (4 ^ (n + 1) / 2) * R ^ n := by
          apply mul_le_mul _ hpow (pow_nonneg (abs_nonneg t) _) (by positivity)
          linarith [hC]
      _ = 2 * ((4 : ℝ) * R) ^ n := by ring
  have hmain : HasDerivAt
      (fun z => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * z ^ (n + 1))
      (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * y ^ n))
      y :=
    hasDerivAt_tsum_of_isPreconnected hU hopen hconn
      (fun n t _ => by
        have h1 := ((hasDerivAt_pow (n + 1) t).const_mul
          ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)))
        have e1 : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have e2 : n + 1 - 1 = n := by omega
        rw [e1, e2] at h1
        have heq : ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n)
            = ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * t ^ n) :=
          rfl
        rwa [heq] at h1)
      (fun n t ht => hbound n t ht) hy0 hS0 hy
  have hcongr : (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1))
        * (((n : ℝ) + 1) * y ^ n))
      = ∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n := by
    apply tsum_congr
    intro n
    have hN : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  rw [hcongr] at hmain
  exact hmain

/-- Cauchy product: the Catalan series times the b-series is the derivative series. -/
theorem S_mul_B (y : ℝ) (hy : |y| < 1 / 4) :
    (∑' n, (catalan n : ℝ) * y ^ n) * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n)
      = ∑' n : ℕ, (((n : ℝ) + 1) * (catalan (n + 1) : ℝ)) * y ^ n := by
  have hSn := summable_cat_norm y hy
  have hBn := summable_cbnorm y hy
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hSn hBn]
  apply tsum_congr
  intro n
  have hcf := conv_for_deriv n
  have hterm : ∀ k ∈ Finset.range (n + 1),
      ((catalan k : ℝ) * y ^ k) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2 * y ^ (n - k))
        = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * y ^ n := by
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hpow : y ^ k * y ^ (n - k) = y ^ n := by
      rw [← pow_add]
      congr 1
      omega
    calc ((catalan k : ℝ) * y ^ k) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2 * y ^ (n - k))
        = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * (y ^ k * y ^ (n - k)) := by
          ring
      _ = ((catalan k : ℝ) * ((Nat.centralBinom (n - k + 1) : ℝ) / 2)) * y ^ n := by
          rw [hpow]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hcf]

/-- Derivative of the log-Catalan series is the b-series. -/
theorem L_hasDerivAt (R : ℝ) (hR4 : R < 1 / 4) (_hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    HasDerivAt (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
      (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) y := by
  have hmem : |y| < R := by
    have h := Metric.mem_ball.mp hy
    rwa [dist_zero_right, Real.norm_eq_abs] at h
  have hy4 : |y| < 1 / 4 := lt_trans hmem hR4
  have hS := S_hasDerivAt y hy4 R hmem hR4 hR8 y hy
  have hB := S_mul_B y hy4
  have hSne : (∑' n, (catalan n : ℝ) * y ^ n) ≠ 0 := ne_of_gt (catalan_tsum_pos y hy4)
  have hlog := hS.log hSne
  have hder : (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n)
          / (∑' n, (catalan n : ℝ) * y ^ n)
      = ∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n := by
    have hS' : (∑' n, (catalan (n + 1) : ℝ) * ((n : ℝ) + 1) * y ^ n)
        = (∑' n, (catalan n : ℝ) * y ^ n) * (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * y ^ n) := by
      rw [hB]
      apply tsum_congr
      intro n
      ring
    rw [hS', div_eq_iff hSne]
    exact mul_comm _ _
  rwa [hder] at hlog

theorem S_tsum_zero : (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n) = 1 := by
  have hS := summable_cat 0 (by norm_num)
  rw [hS.tsum_eq_zero_add]
  have htail : (∑' n, (catalan (n + 1) : ℝ) * (0 : ℝ) ^ (n + 1)) = 0 := by
    have hzero : (fun n => (catalan (n + 1) : ℝ) * (0 : ℝ) ^ (n + 1)) = fun _ => 0 := by
      funext n
      simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
    rw [hzero]
    exact tsum_zero
  rw [htail]
  simp [catalan_zero]

theorem H_tsum_zero :
    (∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
    = 0 := by
  have hzero : (fun n => ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1))
      = fun _ => 0 := by
    funext n
    simp only [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [hzero]
  exact tsum_zero

/-- The log-Catalan series equals the integrated b-series on the ball. -/
theorem L_eq_H (R : ℝ) (hR4 : R < 1 / 4) (hR0 : 0 < R) (hR8 : 1 / 8 ≤ R)
    (y : ℝ) (hy : y ∈ Metric.ball (0 : ℝ) R) :
    Real.log (∑' n, (catalan n : ℝ) * y ^ n)
      = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * y ^ (n + 1) := by
  have hopen : IsOpen (Metric.ball (0 : ℝ) R) := Metric.isOpen_ball
  have hconn : IsPreconnected (Metric.ball (0 : ℝ) R) := (convex_ball 0 R).isPreconnected
  have hy0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) R :=
    Metric.mem_ball.mpr (by rw [dist_self]; exact hR0)
  have hL : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
        (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n) t :=
    fun t ht => L_hasDerivAt R hR4 hR0 hR8 t ht
  have hH : ∀ t ∈ Metric.ball (0 : ℝ) R,
      HasDerivAt
        (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
        (∑' n, (Nat.centralBinom (n + 1) : ℝ) / 2 * t ^ n) t :=
    fun t ht => H_hasDerivAt R hR4 hR0 t ht
  have hdL : DifferentiableOn ℝ (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hL t ht).differentiableAt).differentiableWithinAt
  have hdH : DifferentiableOn ℝ
      (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1))
      (Metric.ball (0 : ℝ) R) :=
    fun t ht => ((hH t ht).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn
      (deriv (fun t => Real.log (∑' n, (catalan n : ℝ) * t ^ n)))
      (deriv (fun t => ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * t ^ (n + 1)))
      (Metric.ball (0 : ℝ) R) := by
    intro t ht
    rw [(hL t ht).deriv, (hH t ht).deriv]
  have h0 : Real.log (∑' n, (catalan n : ℝ) * (0 : ℝ) ^ n)
      = ∑' n, ((Nat.centralBinom (n + 1) : ℝ) / 2 / ((n : ℝ) + 1)) * (0 : ℝ) ^ (n + 1) := by
    rw [S_tsum_zero, H_tsum_zero, Real.log_one]
  have heq := IsOpen.eqOn_of_deriv_eq hopen hconn hdL hdH hderiv hy0 h0
  exact heq hy

end MetaMathlibExt
end

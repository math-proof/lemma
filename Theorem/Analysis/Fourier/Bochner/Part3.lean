/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular
import Def.Analysis.Fourier.Bochner.Part2


section

open MeasureTheory Complex

open scoped BigOperators

namespace Fourier.BochnerWanted

/-- Positivity of step sizes. -/
lemma bochnerH_pos (n : ℕ) : 0 < bochnerH n := by
  simp only [bochnerH]
  positivity

/-- Degrees are at least one. -/
lemma bochnerN_ge_one (n : ℕ) : 1 ≤ bochnerN n := by
  simp only [bochnerN]
  calc (1 : ℕ) = 1 ^ 2 := by simp
    _ ≤ (n + 1) ^ 2 := by
      apply Nat.pow_le_pow_left (by omega : 1 ≤ n + 1) 2

/-- Step sizes are at most one. -/
lemma bochnerH_le_one (n : ℕ) : bochnerH n ≤ 1 := by
  simp only [bochnerH]
  rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Step sizes tend to zero. -/
lemma bochnerH_tendsto :
    Filter.Tendsto bochnerH Filter.atTop (nhds 0) := by
  unfold bochnerH
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Degrees tend to infinity. -/
lemma bochnerN_tendsto_atTop :
    Filter.Tendsto bochnerN Filter.atTop Filter.atTop := by
  unfold bochnerN
  refine Filter.Tendsto.atTop_pow ?_ (by norm_num : 0 < 2)
  exact Filter.tendsto_add_atTop_nat 1

/-- Products `N_n * h_n = n+1` tend to infinity. -/
lemma bochnerHN_tendsto_atTop :
    Filter.Tendsto (fun n => (bochnerN n : ℝ) * bochnerH n)
      Filter.atTop Filter.atTop := by
  have heq : (fun n => (bochnerN n : ℝ) * bochnerH n)
      = (fun n : ℕ => (n : ℝ) + 1) := by
    funext n
    simp only [bochnerN, bochnerH]
    push_cast
    field_simp
  rw [heq]
  have hbase : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono (fun n => by simp) hbase

/-- Rounding error for the lattice index. -/
lemma bochnerM_round_le (t : ℝ) (n : ℕ) :
    |t / bochnerH n - ((bochnerM t n : ℤ) : ℝ)| ≤ 1 / 2 :=
  abs_sub_round _

/-- Distance from `t` to the rounded lattice point. -/
lemma bochnerM_mul_sub_le (t : ℝ) (n : ℕ) :
    |t - ((bochnerM t n : ℤ) : ℝ) * bochnerH n| ≤ bochnerH n / 2 := by
  have hh : 0 < bochnerH n := bochnerH_pos n
  have h0 := bochnerM_round_le t n
  have heq : t - ((bochnerM t n : ℤ) : ℝ) * bochnerH n
      = (t / bochnerH n - ((bochnerM t n : ℤ) : ℝ)) * bochnerH n := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hh]
  calc |(t / bochnerH n - ((bochnerM t n : ℤ) : ℝ))| * bochnerH n
      ≤ (1 / 2) * bochnerH n :=
        mul_le_mul_of_nonneg_right h0 (le_of_lt hh)
    _ = bochnerH n / 2 := by ring

/-- Rounded lattice points converge to `t`. -/
lemma bochnerM_mul_tendsto (t : ℝ) :
    Filter.Tendsto (fun n => ((bochnerM t n : ℤ) : ℝ) * bochnerH n)
      Filter.atTop (nhds t) := by
  have hH2 : Filter.Tendsto (fun n => bochnerH n / 2) Filter.atTop (nhds 0) := by
    simpa using bochnerH_tendsto.div_const 2
  have hbound : ∀ n, dist (((bochnerM t n : ℤ) : ℝ) * bochnerH n) t
      ≤ bochnerH n / 2 := by
    intro n
    rw [Real.dist_eq, abs_sub_comm]
    exact bochnerM_mul_sub_le t n
  have hdist : Filter.Tendsto
      (fun n => dist (((bochnerM t n : ℤ) : ℝ) * bochnerH n) t)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => dist_nonneg) hbound hH2
  exact tendsto_iff_dist_tendsto_zero.mpr hdist

/-- Fejér weight-sum identity: the weights sum to one when `f 0 = 1`. -/
lemma bochnerWeight_sum_eq_one
    {f : ℝ → ℂ}
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (f0 : f 0 = 1) (h : ℝ) (hh : 0 < h) (N : ℕ) (hN : 1 ≤ N) :
    ∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r = 1 := by
  have hNeC : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hw : ∀ r ∈ Finset.range (2 * N), 0 ≤ bochnerWeight f h N r := by
    intro r _
    have hKre := (bochnerKernel_im_eq_zero_and_re_nonneg hpd h N
      (bochnerNode h N r)).2
    simp only [bochnerWeight]
    exact div_nonneg hKre (by positivity)
  have h0h : (((0 : ℤ)) : ℝ) * h = 0 := by simp
  have hN80 := charFun_bochnerApprox_lattice hpd h hh N hN 0 (by simp)
  simp only [bochnerApprox] at hN80
  rw [h0h] at hN80
  have h70 := charFun_finsetSum_smul_dirac (Finset.range (2 * N))
    (bochnerNode h N) (bochnerWeight f h N) hw 0
  rw [h70] at hN80
  have hcexp0 : ∀ r ∈ Finset.range (2 * N),
      cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I) = 1 := by
    intro r _
    have harg0 : (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I : ℂ) = 0 := by
      simp
    rw [harg0, Complex.exp_zero]
  have hLHS : (∑ r ∈ Finset.range (2 * N),
      (((bochnerWeight f h N r : ℝ)) : ℂ)
        * cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I))
      = (((∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r : ℝ)) : ℂ) := by
    rw [show (∑ r ∈ Finset.range (2 * N),
        (((bochnerWeight f h N r : ℝ)) : ℂ)
          * cexp (↑(0 : ℝ) * ↑(bochnerNode h N r) * Complex.I))
        = ∑ r ∈ Finset.range (2 * N),
          (((bochnerWeight f h N r : ℝ)) : ℂ) from
      Finset.sum_congr rfl (fun r hr => by rw [hcexp0 r hr, mul_one])]
    exact (Complex.ofReal_sum _ _).symm
  have hRHS : (((N : ℂ) - (((|(0 : ℤ)| : ℤ)) : ℂ)) / (N : ℂ))
      * f 0 = 1 := by
    rw [f0, mul_one, abs_zero, Int.cast_zero, sub_zero, div_self hNeC]
  rw [hLHS, hRHS] at hN80
  have hre := congrArg Complex.re hN80
  simpa using hre

/-- Modulus bound for the first term via the pointwise Fejér estimate. -/
lemma bochnerCharFun_sub_bound
    {f : ℝ → ℂ}
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (f0 : f 0 = 1) (h : ℝ) (hh : 0 < h) (N : ℕ) (hN : 1 ≤ N)
    (t : ℝ) (m : ℤ) (hs : |t - (m : ℝ) * h| ≤ h / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ‖charFun (bochnerApprox f h N) t
        - charFun (bochnerApprox f h N) ((m : ℝ) * h)‖
      ≤ ε + (∑ r ∈ Finset.range (2 * N),
        bochnerWeight f h N r * (1 - Real.cos (h * bochnerNode h N r))) / ε := by
  have hw : ∀ r ∈ Finset.range (2 * N), 0 ≤ bochnerWeight f h N r := by
    intro r _
    have hKre := (bochnerKernel_im_eq_zero_and_re_nonneg hpd h N
      (bochnerNode h N r)).2
    simp only [bochnerWeight]
    exact div_nonneg hKre (by positivity)
  have hsum1 := bochnerWeight_sum_eq_one hpd f0 h hh N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hNh : (0 : ℝ) < (N : ℝ) * h := mul_pos hNpos hh
  have hξ : ∀ r ∈ Finset.range (2 * N),
      |bochnerNode h N r| ≤ Real.pi / h := by
    intro r hr
    have hrN : r < 2 * N := Finset.mem_range.mp hr
    have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    have hr2 : (r : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hrN
    have h1 : |(r : ℝ) - (N : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le]
      constructor <;> linarith
    have hle : Real.pi * |(r : ℝ) - (N : ℝ)| ≤ Real.pi * (N : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
    simp only [bochnerNode]
    rw [abs_div, abs_mul, abs_of_pos hNh, abs_of_pos Real.pi_pos]
    rw [div_le_div_iff₀ hNh hh]
    calc Real.pi * |(r : ℝ) - (N : ℝ)| * h
        ≤ Real.pi * (N : ℝ) * h :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hh)
      _ = Real.pi * ((N : ℝ) * h) := by ring
  have hCt : charFun (bochnerApprox f h N) t
      = ∑ r ∈ Finset.range (2 * N),
        (((bochnerWeight f h N r : ℝ)) : ℂ)
          * cexp (↑t * ↑(bochnerNode h N r) * Complex.I) := by
    have hbase := charFun_finsetSum_smul_dirac (Finset.range (2 * N))
      (bochnerNode h N) (bochnerWeight f h N) hw t
    simpa only [bochnerApprox] using hbase
  have hCm : charFun (bochnerApprox f h N) ((m : ℝ) * h)
      = ∑ r ∈ Finset.range (2 * N),
        (((bochnerWeight f h N r : ℝ)) : ℂ)
          * cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I) := by
    have hbase := charFun_finsetSum_smul_dirac (Finset.range (2 * N))
      (bochnerNode h N) (bochnerWeight f h N) hw ((m : ℝ) * h)
    simpa only [bochnerApprox] using hbase
  have hdiff_le : ∀ r ∈ Finset.range (2 * N),
      ‖cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
          - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)‖
        ≤ ε + (1 - Real.cos (h * bochnerNode h N r)) / ε := by
    intro r hr
    have hx := hξ r hr
    have hs0 : |t - (m : ℝ) * h| ≤ h / 2 := hs
    have hN10 := norm_exp_sub_one_le_of_abs_le h (t - (m : ℝ) * h)
      (bochnerNode h N r) ε hh hs0 hx hε
    have harg : (↑t * ↑(bochnerNode h N r) * Complex.I : ℂ)
        = (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)
          + (↑(t - (m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I) := by
      push_cast
      ring
    have hfactor : cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
          - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)
        = cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r) * Complex.I)
          * (cexp (↑(t - (m : ℝ) * h) * ↑(bochnerNode h N r)
            * Complex.I) - 1) := by
      rw [harg, Complex.exp_add]
      ring
    have hnorm1 : ‖cexp (↑((m : ℝ) * h)
        * ↑(bochnerNode h N r) * Complex.I)‖ = 1 :=
      norm_cexp_ofReal_mul ((m : ℝ) * h) (bochnerNode h N r)
    rw [hfactor, norm_mul, hnorm1, one_mul]
    exact hN10
  have hDiffEq : charFun (bochnerApprox f h N) t
        - charFun (bochnerApprox f h N) ((m : ℝ) * h)
      = ∑ r ∈ Finset.range (2 * N),
        (((bochnerWeight f h N r : ℝ)) : ℂ)
          * (cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
            - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r)
              * Complex.I)) := by
    rw [hCt, hCm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hnormW : ∀ r ∈ Finset.range (2 * N),
      ‖(((bochnerWeight f h N r : ℝ)) : ℂ)
          * (cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
            - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r)
              * Complex.I))‖
        = bochnerWeight f h N r
          * ‖cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
            - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r)
              * Complex.I)‖ := by
    intro r hr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw r hr)]
  calc ‖charFun (bochnerApprox f h N) t
          - charFun (bochnerApprox f h N) ((m : ℝ) * h)‖
        ≤ ∑ r ∈ Finset.range (2 * N),
          ‖(((bochnerWeight f h N r : ℝ)) : ℂ)
            * (cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
              - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r)
                * Complex.I))‖ := by
          rw [hDiffEq]
          exact norm_sum_le _ _
      _ = ∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r
          * ‖cexp (↑t * ↑(bochnerNode h N r) * Complex.I)
            - cexp (↑((m : ℝ) * h) * ↑(bochnerNode h N r)
              * Complex.I)‖ :=
          Finset.sum_congr rfl (fun r hr => hnormW r hr)
      _ ≤ ∑ r ∈ Finset.range (2 * N), bochnerWeight f h N r
          * (ε + (1 - Real.cos (h * bochnerNode h N r)) / ε) := by
          apply Finset.sum_le_sum
          intro r hr
          apply mul_le_mul_of_nonneg_left (hdiff_le r hr) (hw r hr)
      _ = ε + (∑ r ∈ Finset.range (2 * N),
          bochnerWeight f h N r * (1 - Real.cos (h * bochnerNode h N r))) / ε := by
          have hsplit : ∀ r ∈ Finset.range (2 * N),
              bochnerWeight f h N r
                * (ε + (1 - Real.cos (h * bochnerNode h N r)) / ε)
              = bochnerWeight f h N r * ε
                + (bochnerWeight f h N r
                  * (1 - Real.cos (h * bochnerNode h N r))) / ε := by
            intro r _
            ring
          rw [Finset.sum_congr rfl (fun r hr => hsplit r hr)]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
          rw [hsum1, one_mul]

/-- The rounded index over degree tends to zero: `|m_n| / N_n → 0`. -/
lemma bochnerM_abs_div_N_tendsto (t : ℝ) :
    Filter.Tendsto
      (fun n => ((|bochnerM t n| : ℤ) : ℝ) / (bochnerN n : ℝ))
      Filter.atTop (nhds 0) := by
  have hH0 := bochnerH_tendsto
  have hg_lim : Filter.Tendsto (fun n => (|t| + 1) * bochnerH n)
      Filter.atTop (nhds 0) := by
    have hcm := hH0.const_mul (|t| + 1)
    simpa using hcm
  apply squeeze_zero (fun n => div_nonneg
    (by exact_mod_cast abs_nonneg (bochnerM t n))
    (Nat.cast_nonneg _)) _ hg_lim
  intro n
  have hh := bochnerH_pos n
  have hHle := bochnerH_le_one n
  have hNge := bochnerN_ge_one n
  have hNposR : (0 : ℝ) < (bochnerN n : ℝ) := by
    have hpos : 0 < bochnerN n := by omega
    exact_mod_cast hpos
  have heqHN : (bochnerN n : ℝ) * bochnerH n = (n : ℝ) + 1 := by
    simp only [bochnerN, bochnerH]
    push_cast
    field_simp
  have hround := bochnerM_round_le t n
  have hcast : (((|bochnerM t n| : ℤ)) : ℝ)
      = |(((bochnerM t n : ℤ)) : ℝ)| := Int.cast_abs
  have hdiv : |t / bochnerH n| = |t| / bochnerH n := by
    rw [abs_div, abs_of_pos hh]
  have htri : |(((bochnerM t n : ℤ)) : ℝ)|
      ≤ |t| / bochnerH n + 1 / 2 := by
    calc |(((bochnerM t n : ℤ)) : ℝ)|
          ≤ |(((bochnerM t n : ℤ)) : ℝ) - t / bochnerH n|
            + |t / bochnerH n| := by
            have hle := abs_add_le
              ((((bochnerM t n : ℤ)) : ℝ) - t / bochnerH n)
              (t / bochnerH n)
            have heq : ((((bochnerM t n : ℤ)) : ℝ) - t / bochnerH n)
                + t / bochnerH n
              = (((bochnerM t n : ℤ)) : ℝ) := by ring
            rw [heq] at hle
            exact hle
        _ = |t / bochnerH n - (((bochnerM t n : ℤ)) : ℝ)|
            + |t / bochnerH n| := by
            rw [abs_sub_comm]
        _ ≤ 1 / 2 + |t / bochnerH n| := by
            gcongr
        _ = |t| / bochnerH n + 1 / 2 := by
            rw [hdiv]
            ring
  have h1h : (1 : ℝ) ≤ 1 / bochnerH n := by
    rw [le_div_iff₀ hh]
    simpa using hHle
  have hhalf : (1 : ℝ) / 2 ≤ 1 / bochnerH n := by
    calc (1 : ℝ) / 2 ≤ 1 := by norm_num
      _ ≤ 1 / bochnerH n := h1h
  have h_abs_le : (((|bochnerM t n| : ℤ)) : ℝ)
      ≤ (|t| + 1) / bochnerH n := by
    rw [hcast]
    calc |(((bochnerM t n : ℤ)) : ℝ)|
        ≤ |t| / bochnerH n + 1 / 2 := htri
      _ ≤ |t| / bochnerH n + 1 / bochnerH n := by gcongr
      _ = (|t| + 1) / bochnerH n := by ring
  have h_step : (((|bochnerM t n| : ℤ)) : ℝ) / (bochnerN n : ℝ)
      ≤ ((|t| + 1) / bochnerH n) / (bochnerN n : ℝ) := by
    gcongr
  have h_eq1 : ((|t| + 1) / bochnerH n) / (bochnerN n : ℝ)
      = (|t| + 1) / (bochnerH n * (bochnerN n : ℝ)) := by
    rw [div_div]
  have h_eq2 : bochnerH n * (bochnerN n : ℝ) = (n : ℝ) + 1 := by
    rw [mul_comm]
    exact heqHN
  have h_eq3 : (|t| + 1) / ((n : ℝ) + 1) = (|t| + 1) * bochnerH n := by
    simp only [bochnerH, mul_one_div]
  rw [h_eq1, h_eq2, h_eq3] at h_step
  exact h_step

/-- Pointwise convergence of the Fejér approximations. -/
lemma bochnerSeq_charFun_tendsto
    {f : ℝ → ℂ} (hcont : Continuous f) (f0 : f 0 = 1)
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
      S.im = 0 ∧ 0 ≤ S.re)
    (t : ℝ) :
    Filter.Tendsto (fun n => charFun (bochnerSeq f n) t)
      Filter.atTop (nhds (f t)) := by
  have hH0 := bochnerH_tendsto
  have hM0 := bochnerM_mul_tendsto t
  have h_abs_div := bochnerM_abs_div_N_tendsto t
  have h_f_mh : Filter.Tendsto
      (fun n => f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
      Filter.atTop (nhds (f t)) :=
    (hcont.tendsto t).comp hM0
  have h_f_h : Filter.Tendsto (fun n => f (bochnerH n))
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n => f (bochnerH n))
        Filter.atTop (nhds (f 0)) :=
      (hcont.tendsto 0).comp hH0
    simpa [f0] using h1
  have h_h2 : Filter.Tendsto (fun n => bochnerH n ^ 2)
      Filter.atTop (nhds 0) := by
    simpa [pow_two] using hH0.mul hH0
  have h_frac_real : Filter.Tendsto (fun n => (1 : ℝ) - bochnerH n ^ 2)
      Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub h_h2
  have h_h2_eq : ∀ n, bochnerH n ^ 2 = 1 / (bochnerN n : ℝ) := by
    intro n
    simp only [bochnerH, bochnerN]
    push_cast
    field_simp
  have h_real_eq : ∀ n,
      ((bochnerN n : ℝ) - 1) / (bochnerN n : ℝ)
        = 1 - bochnerH n ^ 2 := by
    intro n
    have hNpos : (0 : ℝ) < (bochnerN n : ℝ) := by
      have hpos : 0 < bochnerN n := by
        have hge := bochnerN_ge_one n
        omega
      exact_mod_cast hpos
    rw [h_h2_eq n, sub_div, div_self (ne_of_gt hNpos)]
  have h_lat1 : ∀ n, charFun (bochnerSeq f n) (bochnerH n)
      = ((((bochnerN n : ℕ)) : ℂ) - 1) / ((((bochnerN n : ℕ)) : ℂ))
        * f (bochnerH n) := by
    intro n
    have hN := bochnerN_ge_one n
    have hm1 : |(1 : ℤ)| ≤ ((bochnerN n : ℕ) : ℤ) := by
      have h1 : (1 : ℤ) ≤ ((bochnerN n : ℕ) : ℤ) := by
        exact_mod_cast hN
      calc |(1 : ℤ)| = 1 := abs_one
        _ ≤ ((bochnerN n : ℕ) : ℤ) := h1
    have hlat := charFun_bochnerApprox_lattice hpd (bochnerH n)
      (bochnerH_pos n) (bochnerN n) hN 1 hm1
    have h1h : (((1 : ℤ)) : ℝ) * bochnerH n = bochnerH n := by simp
    have h_abs1 : ((((|(1 : ℤ)| : ℤ))) : ℂ) = 1 := by simp
    simp only [bochnerSeq] at hlat ⊢
    rw [h1h, h_abs1] at hlat
    exact hlat
  have h_complex_eq : ∀ n,
      ((((bochnerN n : ℕ)) : ℂ) - 1) / ((((bochnerN n : ℕ)) : ℂ))
        = ((((1 - bochnerH n ^ 2 : ℝ))) : ℂ) := by
    intro n
    rw [← h_real_eq n]
    norm_cast
  have h_c : Filter.Tendsto
      (fun n => ((((1 - bochnerH n ^ 2 : ℝ))) : ℂ))
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto
        (fun n => ((((1 - bochnerH n ^ 2 : ℝ))) : ℂ))
        Filter.atTop (nhds ((((1 : ℝ))) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp h_frac_real
    simpa using h1
  have h_lat_tend : Filter.Tendsto
      (fun n => charFun (bochnerSeq f n) (bochnerH n))
      Filter.atTop (nhds 1) := by
    have h_eq : ∀ n, charFun (bochnerSeq f n) (bochnerH n)
        = ((((1 - bochnerH n ^ 2 : ℝ))) : ℂ) * f (bochnerH n) := by
      intro n
      rw [h_lat1 n, h_complex_eq n]
    have h_fun_eq : (fun n => charFun (bochnerSeq f n) (bochnerH n))
        = (fun n => ((((1 - bochnerH n ^ 2 : ℝ))) : ℂ)
          * f (bochnerH n)) :=
        funext (fun n => h_eq n)
    rw [h_fun_eq]
    simpa using h_c.mul h_f_h
  have h_C_eq : ∀ n,
      (∑ r ∈ Finset.range (2 * bochnerN n), bochnerWeight f (bochnerH n)
        (bochnerN n) r
          * (1 - Real.cos (bochnerH n
            * bochnerNode (bochnerH n) (bochnerN n) r)))
        = 1 - (charFun (bochnerSeq f n) (bochnerH n)).re := by
    intro n
    have hN := bochnerN_ge_one n
    have hh := bochnerH_pos n
    have hw : ∀ r ∈ Finset.range (2 * bochnerN n),
        0 ≤ bochnerWeight f (bochnerH n) (bochnerN n) r := by
      intro r _
      have hKre := (bochnerKernel_im_eq_zero_and_re_nonneg hpd
        (bochnerH n) (bochnerN n) (bochnerNode (bochnerH n)
          (bochnerN n) r)).2
      simp only [bochnerWeight]
      exact div_nonneg hKre (by positivity)
    have hsum1 := bochnerWeight_sum_eq_one hpd f0 (bochnerH n) hh
      (bochnerN n) hN
    have hCh : charFun (bochnerSeq f n) (bochnerH n)
        = ∑ r ∈ Finset.range (2 * bochnerN n),
          ((((bochnerWeight f (bochnerH n) (bochnerN n) r : ℝ))) : ℂ)
            * cexp (↑(bochnerH n)
              * ↑(bochnerNode (bochnerH n) (bochnerN n) r)
              * Complex.I) := by
      have hbase := charFun_finsetSum_smul_dirac
        (Finset.range (2 * bochnerN n))
        (bochnerNode (bochnerH n) (bochnerN n))
        (bochnerWeight f (bochnerH n) (bochnerN n)) hw (bochnerH n)
      simpa only [bochnerSeq, bochnerApprox] using hbase
    have hRe : (charFun (bochnerSeq f n) (bochnerH n)).re
        = ∑ r ∈ Finset.range (2 * bochnerN n),
          bochnerWeight f (bochnerH n) (bochnerN n) r
            * Real.cos (bochnerH n
              * bochnerNode (bochnerH n) (bochnerN n) r) := by
      rw [hCh, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro r _
      have hform : (↑(bochnerH n)
          * ↑(bochnerNode (bochnerH n) (bochnerN n) r)
          * Complex.I : ℂ)
          = ↑(bochnerH n
            * bochnerNode (bochnerH n) (bochnerN n) r)
            * Complex.I := by
        push_cast
        ring
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hform, Complex.exp_ofReal_mul_I_re]
    have h_split : ∀ r ∈ Finset.range (2 * bochnerN n),
        bochnerWeight f (bochnerH n) (bochnerN n) r
          * (1 - Real.cos (bochnerH n
            * bochnerNode (bochnerH n) (bochnerN n) r))
          = bochnerWeight f (bochnerH n) (bochnerN n) r
            - bochnerWeight f (bochnerH n) (bochnerN n) r
              * Real.cos (bochnerH n
                * bochnerNode (bochnerH n) (bochnerN n) r) := by
      intro r _
      ring
    rw [Finset.sum_congr rfl (fun r hr => h_split r hr),
      Finset.sum_sub_distrib, hsum1, hRe]
  have h_Re_tend : Filter.Tendsto
      (fun n => (charFun (bochnerSeq f n) (bochnerH n)).re)
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto
        (fun n => (charFun (bochnerSeq f n) (bochnerH n)).re)
        Filter.atTop (nhds ((1 : ℂ).re)) :=
      (Complex.continuous_re.tendsto 1).comp h_lat_tend
    simpa [Complex.one_re] using h1
  have h_C_tend : Filter.Tendsto
      (fun n => ∑ r ∈ Finset.range (2 * bochnerN n),
        bochnerWeight f (bochnerH n) (bochnerN n) r
          * (1 - Real.cos (bochnerH n
            * bochnerNode (bochnerH n) (bochnerN n) r)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto
        (fun n => 1 - (charFun (bochnerSeq f n) (bochnerH n)).re)
        Filter.atTop (nhds (1 - 1)) :=
      tendsto_const_nhds.sub h_Re_tend
    simpa [h_C_eq] using h1
  have h_A_tend : Filter.Tendsto
      (fun n => charFun (bochnerSeq f n) t
        - charFun (bochnerSeq f n)
          ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hε0 : (0 : ℝ) < δ / 2 := by linarith
    have hpos : (0 : ℝ) < δ / 2 * (δ / 2) :=
      mul_pos hε0 hε0
    have h_C_ev : ∀ᶠ n in Filter.atTop,
        (∑ r ∈ Finset.range (2 * bochnerN n),
          bochnerWeight f (bochnerH n) (bochnerN n) r
            * (1 - Real.cos (bochnerH n
              * bochnerNode (bochnerH n) (bochnerN n) r)))
          < δ / 2 * (δ / 2) :=
      h_C_tend.eventually (Iio_mem_nhds hpos)
    have h_ev : ∀ᶠ n in Filter.atTop,
        dist (charFun (bochnerSeq f n) t
          - charFun (bochnerSeq f n)
            ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)) 0 < δ := by
      apply h_C_ev.mono
      intro n hn
      have hN := bochnerN_ge_one n
      have hh := bochnerH_pos n
      have hround : |t - ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)|
          ≤ bochnerH n / 2 :=
        bochnerM_mul_sub_le t n
      have hbound := bochnerCharFun_sub_bound hpd f0 (bochnerH n) hh
        (bochnerN n) hN t (bochnerM t n) hround (δ / 2) hε0
      have hdiv : (∑ r ∈ Finset.range (2 * bochnerN n),
          bochnerWeight f (bochnerH n) (bochnerN n) r
            * (1 - Real.cos (bochnerH n
              * bochnerNode (bochnerH n) (bochnerN n) r))) / (δ / 2)
          < δ / 2 := by
        rw [div_lt_iff₀ hε0]
        exact hn
      have hlt : ‖charFun (bochnerSeq f n) t
          - charFun (bochnerSeq f n)
            ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)‖ < δ := by
        calc ‖charFun (bochnerSeq f n) t
              - charFun (bochnerSeq f n)
                ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)‖
              ≤ δ / 2 + (∑ r ∈ Finset.range (2 * bochnerN n),
                bochnerWeight f (bochnerH n) (bochnerN n) r
                  * (1 - Real.cos (bochnerH n
                    * bochnerNode (bochnerH n) (bochnerN n) r)))
                / (δ / 2) :=
              hbound
          _ < δ / 2 + δ / 2 := by gcongr
          _ = δ := by ring
      simpa [dist_zero_right] using hlt
    exact Filter.eventually_atTop.mp h_ev
  have h_ev_le : ∀ᶠ n in Filter.atTop,
      |(bochnerM t n)| ≤ ((bochnerN n : ℕ) : ℤ) := by
    have h1 : ∀ᶠ n in Filter.atTop,
        ((((|(bochnerM t n)| : ℤ)) : ℝ) / (bochnerN n : ℝ)) < 1 :=
      h_abs_div.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    apply h1.mono
    intro n hn
    have hNpos : (0 : ℝ) < (bochnerN n : ℝ) := by
      have hpos : 0 < bochnerN n := by
        have hge := bochnerN_ge_one n
        omega
      exact_mod_cast hpos
    have hltR : ((((|(bochnerM t n)| : ℤ))) : ℝ) < (bochnerN n : ℝ) := by
      have hdiv := (div_lt_one hNpos).mp hn
      exact hdiv
    have hlt : |(bochnerM t n)| < ((bochnerN n : ℕ) : ℤ) := by
      exact_mod_cast hltR
    exact le_of_lt hlt
  have h_B_tend : Filter.Tendsto
      (fun n => charFun (bochnerSeq f n)
        ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
          - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
      Filter.atTop (nhds 0) := by
    have h_r_tend : Filter.Tendsto
        (fun n => ((((|(bochnerM t n)| : ℤ)) : ℝ)
          / (bochnerN n : ℝ)))
        Filter.atTop (nhds 0) :=
      h_abs_div
    have h_smul_tend : Filter.Tendsto
        (fun n => ((((|(bochnerM t n)| : ℤ)) : ℝ)
          / (bochnerN n : ℝ))
            • f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        Filter.atTop (nhds ((0 : ℝ) • f t)) :=
      h_r_tend.smul h_f_mh
    have h_zero : Filter.Tendsto
        (fun n => ((((|(bochnerM t n)| : ℤ)) : ℝ)
          / (bochnerN n : ℝ))
            • f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        Filter.atTop (nhds 0) := by
      simpa using h_smul_tend
    have h_eq_ev : ∀ᶠ n in Filter.atTop,
        charFun (bochnerSeq f n)
            ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
              - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
          = -((((((|(bochnerM t n)| : ℤ)) : ℝ)
            / (bochnerN n : ℝ)) : ℝ) : ℂ)
            * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
      apply h_ev_le.mono
      intro n hn
      have hN := bochnerN_ge_one n
      have hh := bochnerH_pos n
      have hNeC : ((((bochnerN n : ℕ))) : ℂ) ≠ 0 := by
        exact_mod_cast (by omega : bochnerN n ≠ 0)
      have hlat := charFun_bochnerApprox_lattice hpd (bochnerH n) hh
        (bochnerN n) hN (bochnerM t n) hn
      simp only [bochnerSeq] at hlat ⊢
      have h_eq1 : ((((bochnerN n : ℕ)) : ℂ)
          - ((((|(bochnerM t n)| : ℤ))) : ℂ))
          / ((((bochnerN n : ℕ))) : ℂ)
          - 1
          = -(((((|(bochnerM t n)| : ℤ))) : ℂ)
            / ((((bochnerN n : ℕ))) : ℂ)) := by
        field_simp
        ring
      have h_eq2 : ((((|(bochnerM t n)| : ℤ))) : ℂ)
          / ((((bochnerN n : ℕ))) : ℂ)
          = ((((((|(bochnerM t n)| : ℤ)) : ℝ)
            / (bochnerN n : ℝ)) : ℝ) : ℂ) := by
        norm_cast
      calc charFun (bochnerApprox f (bochnerH n) (bochnerN n))
              ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
              - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
            = ((((bochnerN n : ℕ)) : ℂ)
              - ((((|(bochnerM t n)| : ℤ))) : ℂ))
              / ((((bochnerN n : ℕ))) : ℂ)
              * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
              - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
              rw [hlat]
        _ = ((((bochnerN n : ℕ)) : ℂ)
              - ((((|(bochnerM t n)| : ℤ))) : ℂ))
              / ((((bochnerN n : ℕ))) : ℂ)
              * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
              - 1 * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
              rw [one_mul]
        _ = (((((bochnerN n : ℕ)) : ℂ)
              - ((((|(bochnerM t n)| : ℤ))) : ℂ))
              / ((((bochnerN n : ℕ))) : ℂ) - 1)
              * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
              ring
        _ = -(((((|(bochnerM t n)| : ℤ))) : ℂ)
              / ((((bochnerN n : ℕ))) : ℂ))
              * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
              rw [h_eq1]
        _ = -((((((|(bochnerM t n)| : ℤ)) : ℝ)
              / (bochnerN n : ℝ)) : ℝ) : ℂ)
              * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) := by
              rw [h_eq2]
    have h_neg_tend : Filter.Tendsto
        (fun n => -((((((|(bochnerM t n)| : ℤ)) : ℝ)
          / (bochnerN n : ℝ)) : ℝ) : ℂ)
          * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto
          (fun n => ((((|(bochnerM t n)| : ℤ)) : ℝ)
            / (bochnerN n : ℝ))
              • f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
          Filter.atTop (nhds 0) :=
        h_zero
      have h_eq : ∀ n,
          -((((((|(bochnerM t n)| : ℤ)) : ℝ)
            / (bochnerN n : ℝ)) : ℝ) : ℂ)
            * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
            = -(((((|(bochnerM t n)| : ℤ)) : ℝ)
              / (bochnerN n : ℝ))
                • f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)) := by
        intro n
        simp only [Complex.real_smul, neg_mul]
      simpa [h_eq] using h1.neg
    have h_eq_fun : (fun n => charFun (bochnerSeq f n)
        ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
          - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        =ᶠ[Filter.atTop] (fun n => -((((((|(bochnerM t n)| : ℤ)) : ℝ)
          / (bochnerN n : ℝ)) : ℝ) : ℂ)
          * f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)) :=
      h_eq_ev
    exact Filter.Tendsto.congr' h_eq_fun.symm h_neg_tend
  have h_C'_tend : Filter.Tendsto
      (fun n => f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) - f t)
      Filter.atTop (nhds 0) := by
    simpa using h_f_mh.sub_const (f t)
  have h_sum_tend : Filter.Tendsto
      (fun n => (charFun (bochnerSeq f n) t
        - charFun (bochnerSeq f n)
          ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        + ((charFun (bochnerSeq f n)
          ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
            - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
          + (f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) - f t)))
      Filter.atTop (nhds (0 + (0 + 0))) :=
    h_A_tend.add (h_B_tend.add h_C'_tend)
  have h_fun_eq : (fun n => (charFun (bochnerSeq f n) t
      - charFun (bochnerSeq f n)
        ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
      + ((charFun (bochnerSeq f n)
        ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n)
          - f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n))
        + (f ((((bochnerM t n : ℤ)) : ℝ) * bochnerH n) - f t)))
      = (fun n => charFun (bochnerSeq f n) t - f t) :=
    funext (fun n => by ring)
  have h_sub_tend : Filter.Tendsto
      (fun n => charFun (bochnerSeq f n) t - f t)
      Filter.atTop (nhds 0) := by
    simpa [h_fun_eq] using h_sum_tend
  have h_add_tend : Filter.Tendsto
      (fun n => (charFun (bochnerSeq f n) t - f t) + f t)
      Filter.atTop (nhds (0 + f t)) :=
    h_sub_tend.add tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using h_add_tend

/--
A function `f : ℝ → ℂ` is continuous, `f 0 = 1`, and positive-definite `∀ n x c, S = ∑_i∑_j
star(c_i) * c_j * f(x_i-x_j) satisfies S.im = 0 ∧ 0 ≤ S.re` iff there exists Borel probability `μ
: Measure ℝ` with `f t = charFun μ t` for all `t`. Source: Bochner's theorem on positive-definite
functions, S. Bochner, Vorlesungen über Fouriersche Integrale 1932 and Math. Ann. 108 (1933); see
Folland, Abstract Harmonic Analysis, Fourier Analysis on Groups; Lean is ℝ→ℂ iff version
continuous f 0=1 positive- definite via double sum iff ∃ Borel probability μ with f = charFun μ,
fixed +I sign via charFun.

Proves `Wanted` entry `bochner`.
-/
theorem bochner
    {f : ℝ → ℂ} :
    (Continuous f ∧ f 0 = 1 ∧
      ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
        let S := ∑ i : Fin n, ∑ j : Fin n, star (c i) * c j * f (x i - x j)
        S.im = 0 ∧ 0 ≤ S.re)
    ↔
    (∃ (μ : Measure ℝ), IsProbabilityMeasure μ ∧ ∀ (t : ℝ), f t = charFun μ t) := by
  constructor
  · rintro ⟨hcont, h0, hpd⟩
    have : ∀ n, IsProbabilityMeasure (bochnerSeq f n) := by
      intro n
      have hN := bochnerN_ge_one n
      have hprob := (bochnerApprox_isProbabilityMeasure_and_support hpd h0
        (bochnerH n) (bochnerH_pos n) (bochnerN n) hN).1
      simpa only [bochnerSeq] using hprob
    have h_tend : ∀ t : ℝ, Filter.Tendsto
        (fun n => charFun (bochnerSeq f n) t)
        Filter.atTop (nhds (f t)) := by
      intro t
      exact bochnerSeq_charFun_tendsto hcont h0 hpd t
    obtain ⟨μ, hprob, hchar⟩ :=
      exists_charFun_eq_of_tendsto_charFun (ν := bochnerSeq f)
        (g := f) hcont.continuousAt h_tend
    exact ⟨μ, hprob, fun t => (hchar t).symm⟩
  · rintro ⟨μ, hprob, hf⟩
    exact @bochner_mpr _ μ hprob hf

end Fourier.BochnerWanted
end

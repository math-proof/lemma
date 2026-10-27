/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology

open Filter

noncomputable section

theorem chap9c_nonneg (k : ℕ) : 0 ≤ chap9c k := by
  unfold chap9c
  apply div_nonneg (Nat.cast_nonneg _)
  apply pow_nonneg
  norm_num

theorem chap9c_le_one (k : ℕ) : chap9c k ≤ 1 := by
  unfold chap9c
  have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h := Nat.choose_le_two_pow (2 * k) k
    have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
      Nat.cast_le.mpr h
    rwa [Nat.cast_pow, Nat.cast_two] at h2
  have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
  exact div_le_one_of_le₀ hchoose (le_of_lt hP)

theorem Dpos1_aux (k : ℕ) : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ)) := by
  apply Nat.cast_pos.mpr
  omega

theorem inv_D_le_one_aux (k : ℕ) : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ)) ≤ 1 := by
  rw [div_le_one (Dpos1_aux k)]
  have h : (1 : ℕ) ≤ 2 * k + 1 := by omega
  exact_mod_cast h

theorem chap9S_eq_aux (u : ℝ) (k : ℕ) :
    chap9S u k = chap9c k * u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chap9S chap9c
  have hP : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  have hD : ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux k)
  field_simp

theorem chap9c_zero_eq : chap9c 0 = 1 := by
  unfold chap9c
  simp

theorem chap9c_succ (n : ℕ) :
    chap9c (n + 1) = chap9c n * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
  have hcb := Nat.succ_mul_centralBinom_succ n
  have hcbR : (((n : ℝ) + 1)) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hcb
    push_cast at h
    linarith [h]
  have hcb_eq : ∀ m : ℕ, ((Nat.choose (2 * m) m : ℕ) : ℝ)
      = ((Nat.centralBinom m : ℕ) : ℝ) := by
    intro m
    rw [Nat.centralBinom_eq_two_mul_choose]
  have hpow : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
    have : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [this, pow_add]
    norm_num [pow_two]
    ring
  have hn1 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have h2n2 : ((((2 * n + 2 : ℕ)) : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < 2 * n + 2 := by omega
    exact_mod_cast ne_of_gt this
  have hP : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  unfold chap9c
  rw [hcb_eq (n + 1), hcb_eq n, hpow]
  have hcast1 : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * n + 1 : ℕ)) : ℝ)) = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hcbR' : ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * (((2 * n + 1 : ℕ)) : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)
        / ((((n + 1 : ℕ)) : ℝ)) := by
    rw [eq_div_iff hn1, hcast1, hcast2]
    linarith [hcbR]
  rw [hcbR']
  have hcast : ((((2 * n + 2 : ℕ)) : ℝ)) = 2 * ((((n + 1 : ℕ)) : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

theorem multichoose_half_succ (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = Ring.multichoose (1 / 2 : ℝ) n
        * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) (n + 1)
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [nsmul_eq_mul] at h1 h0
  have e1 := Polynomial.ascPochhammer_smeval_eq_eval (1 / 2 : ℝ) (n + 1)
  have e0 := Polynomial.ascPochhammer_smeval_eq_eval (1 / 2 : ℝ) n
  rw [e1] at h1
  rw [e0] at h0
  have hsucc : (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ)
      = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) * ((1 / 2 : ℝ) + (n : ℝ)) :=
    ascPochhammer_succ_eval n (1 / 2 : ℝ)
  have hfact1 : ((((n + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hfact0 : ((((n.factorial : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hfact_succ : ((((n + 1).factorial : ℕ)) : ℝ)
      = ((((n + 1 : ℕ)) : ℝ)) * ((((n.factorial : ℕ))) : ℝ) := by
    have h : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    have hc := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hc
    push_cast
    linarith [hc]
  have hcast1 : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * n + 1 : ℕ)) : ℝ)) = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast3 : ((((2 * n + 2 : ℕ)) : ℝ)) = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring
  have hmn : Ring.multichoose (1 / 2 : ℝ) n
      = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / ((((n.factorial : ℕ))) : ℝ) := by
    rw [eq_div_iff hfact0]
    linarith [h0]
  have hmn1 : Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ)
        / ((((n + 1).factorial : ℕ)) : ℝ) := by
    rw [eq_div_iff hfact1]
    linarith [h1]
  rw [hmn1, hmn, hsucc, hfact_succ, hcast1, hcast2, hcast3]
  field_simp
  ring

theorem ring_choose_half_eq_chap9c (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n = chap9c n := by
  induction n with
  | zero =>
    have hz : Ring.choose ((1 / 2 : ℝ) + ((0 : ℕ) : ℝ) - 1) 0 = 1 :=
      Ring.choose_zero_right _
    rw [hz]
    exact chap9c_zero_eq.symm
  | succ n ih =>
    have hmulti : Ring.choose ((1 / 2 : ℝ) + (((n + 1 : ℕ)) : ℝ) - 1) (n + 1)
        = Ring.multichoose (1 / 2 : ℝ) (n + 1) := by
      have h := Ring.multichoose_eq (1 / 2 : ℝ) (n + 1)
      exact h.symm ▸ rfl
    have hmulti0 : Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n
        = Ring.multichoose (1 / 2 : ℝ) n := by
      have h := Ring.multichoose_eq (1 / 2 : ℝ) n
      exact h.symm ▸ rfl
    calc Ring.choose ((1 / 2 : ℝ) + (((n + 1 : ℕ)) : ℝ) - 1) (n + 1)
        = Ring.multichoose (1 / 2 : ℝ) (n + 1) := hmulti
      _ = Ring.multichoose (1 / 2 : ℝ) n
            * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) :=
          multichoose_half_succ n
      _ = chap9c n * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
          rw [← hmulti0, ih]
      _ = chap9c (n + 1) := (chap9c_succ n).symm

theorem abs_sq_lt_one_of_abs_lt_one {u : ℝ} (hu : |u| < 1) :
    |u ^ 2| < 1 := by
  rw [abs_pow]
  have h0 : 0 ≤ |u| := abs_nonneg u
  have h2 : |u| ^ 2 < 1 := by
    have h := pow_lt_one₀ h0 hu (by norm_num : 2 ≠ 0)
    exact h
  exact h2

theorem chap9B_hasSum {u : ℝ} (hu : |u| < 1) :
    HasSum (chap9B u) (1 / Real.sqrt (1 - u ^ 2)) := by
  have hY : |u ^ 2| < 1 := abs_sq_lt_one_of_abs_lt_one hu
  have hmem : (u ^ 2) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    simp only [Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_one.mpr hY
  have hPS := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hHas := hPS.hasSum hmem
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at hHas
  have hterm : (fun n : ℕ => Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n
      * (u ^ 2) ^ n) = chap9B u := by
    funext n
    unfold chap9B
    rw [ring_choose_half_eq_chap9c n]
    congr 1
    rw [← pow_mul]
  rw [hterm] at hHas
  have hsqrt : Real.sqrt (1 - u ^ 2) = (1 - u ^ 2) ^ ((1 / 2 : ℝ)) :=
    Real.sqrt_eq_rpow (1 - u ^ 2)
  rw [hsqrt]
  exact hHas

theorem chap9B_tsum {u : ℝ} (hu : |u| < 1) :
    (∑' k : ℕ, chap9B u k) = 1 / Real.sqrt (1 - u ^ 2) :=
  (chap9B_hasSum hu).tsum_eq

theorem hasDerivAt_chap9A_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun u => chap9A u n) (chap9B y n) y := by
  have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun u : ℝ => u ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul (chap9c n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ))
  have hEq : (fun u => chap9A u n)
      = (fun u => chap9c n * u ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ))) := by
    funext u
    rfl
  rw [hEq]
  have hval : chap9c n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ)) = chap9B y n := by
    unfold chap9B
    field_simp
  rw [hval] at hdiv
  exact hdiv

theorem hasDerivAt_chap9S_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun u => chap9S u n) (chap9Sderiv y n) y := by
  have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
  have hD2 : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun u : ℝ => u ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul (chap9c n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
  have hEq : (fun u => chap9S u n)
      = (fun u => chap9c n * u ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext u
    exact chap9S_eq_aux u n
  rw [hEq]
  have hval : chap9c n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) = chap9Sderiv y n := by
    unfold chap9Sderiv
    have hsq : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
        = ((((2 * n + 1 : ℕ)) : ℝ)) * ((((2 * n + 1 : ℕ)) : ℝ)) := by
      rw [pow_two]
    rw [hsq]
    field_simp
  rw [hval] at hdiv
  exact hdiv

theorem hasDerivAt_chap9T_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun v => chap9T v n) (chap9Tderiv y n) y := by
  have hD2 : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun v : ℝ => v ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul ((-1 : ℝ) ^ n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
  have hEq : (fun v => chap9T v n)
      = (fun v => (-1 : ℝ) ^ n * v ^ (2 * n + 1)
        / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext v
    rfl
  rw [hEq]
  have hval : (-1 : ℝ) ^ n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) = chap9Tderiv y n := by
    unfold chap9Tderiv
    have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
    have hsq : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
        = ((((2 * n + 1 : ℕ)) : ℝ)) * ((((2 * n + 1 : ℕ)) : ℝ)) := by
      rw [pow_two]
    rw [hsq]
    field_simp
  rw [hval] at hdiv
  exact hdiv

theorem abs_pow_two_mul_le {y ρ : ℝ} (hy : |y| < ρ) (_hρ0 : 0 ≤ ρ) (n : ℕ) :
    |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := by
  have hle : |y| ≤ ρ := le_of_lt hy
  have h1 : |y| ^ (2 * n) ≤ ρ ^ (2 * n) :=
    pow_le_pow_left₀ (abs_nonneg y) hle (2 * n)
  have h2 : ρ ^ (2 * n) = (ρ ^ 2) ^ n := by
    rw [← pow_mul]
  rw [h2] at h1
  exact h1

theorem norm_chap9B_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ) (hy : y ∈ Set.Ioo (-ρ) ρ)
    (n : ℕ) : ‖chap9B y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hc0 : 0 ≤ chap9c n := chap9c_nonneg n
  have hc1 : chap9c n ≤ 1 := chap9c_le_one n
  unfold chap9B
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc0]
  calc chap9c n * |y| ^ (2 * n)
      ≤ 1 * (ρ ^ 2) ^ n := by
        apply mul_le_mul hc1 hpow (by positivity) zero_le_one
    _ = (ρ ^ 2) ^ n := one_mul _

theorem norm_chap9Sderiv_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ)
    (hy : y ∈ Set.Ioo (-ρ) ρ) (n : ℕ) :
    ‖chap9Sderiv y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hc0 : 0 ≤ chap9c n := chap9c_nonneg n
  have hc1 : chap9c n ≤ 1 := chap9c_le_one n
  have hD := Dpos1_aux n
  have hDnn : (0 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := le_of_lt hD
  unfold chap9Sderiv
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_nonneg hc0,
    abs_of_nonneg hDnn]
  have h1 : chap9c n * |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := by
    calc chap9c n * |y| ^ (2 * n)
        ≤ 1 * (ρ ^ 2) ^ n := mul_le_mul hc1 hpow (by positivity) zero_le_one
      _ = (ρ ^ 2) ^ n := one_mul _
  have h2 : (1 : ℝ) / ((((2 * n + 1 : ℕ)) : ℝ)) ≤ 1 := inv_D_le_one_aux n
  have h2nn : (0 : ℝ) ≤ 1 / ((((2 * n + 1 : ℕ)) : ℝ)) := by positivity
  have hnn : (0 : ℝ) ≤ (ρ ^ 2) ^ n := by positivity
  calc chap9c n * |y| ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ))
      = (chap9c n * |y| ^ (2 * n)) * (1 / ((((2 * n + 1 : ℕ)) : ℝ))) := by
        rw [div_eq_mul_one_div]
    _ ≤ (ρ ^ 2) ^ n * 1 := mul_le_mul h1 h2 h2nn hnn
    _ = (ρ ^ 2) ^ n := mul_one _

theorem norm_chap9Tderiv_le {ρ y : ℝ} (_hρ0 : 0 ≤ ρ)
    (hy : y ∈ Set.Ioo (-ρ) ρ) (n : ℕ) :
    ‖chap9Tderiv y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hρ0 : 0 ≤ ρ := _hρ0
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hD := Dpos1_aux n
  have hDnn : (0 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := le_of_lt hD
  unfold chap9Tderiv
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg hDnn]
  have h1 : |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := hpow
  have h2 : (1 : ℝ) / ((((2 * n + 1 : ℕ)) : ℝ)) ≤ 1 := inv_D_le_one_aux n
  have h2nn : (0 : ℝ) ≤ 1 / ((((2 * n + 1 : ℕ)) : ℝ)) := by positivity
  have hnn : (0 : ℝ) ≤ (ρ ^ 2) ^ n := by positivity
  calc |y| ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ))
      = (|y| ^ (2 * n)) * (1 / ((((2 * n + 1 : ℕ)) : ℝ))) := by
        rw [div_eq_mul_one_div]
    _ ≤ (ρ ^ 2) ^ n * 1 := mul_le_mul h1 h2 h2nn hnn
    _ = (ρ ^ 2) ^ n := mul_one _

theorem summable_rho_sq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => (ρ ^ 2) ^ n) := by
  have h0 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
  have h1 : ρ ^ 2 < 1 := by nlinarith [hρ0, hρ1, sq_nonneg ρ]
  exact summable_geometric_of_lt_one h0 h1

theorem summable_chap9A_zero : Summable (fun n : ℕ => chap9A 0 n) := by
  have h0 : (fun n : ℕ => chap9A 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9A
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

theorem summable_chap9S_zero : Summable (fun n : ℕ => chap9S 0 n) := by
  have h0 : (fun n : ℕ => chap9S 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9S
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

theorem summable_chap9T_zero : Summable (fun n : ℕ => chap9T 0 n) := by
  have h0 : (fun n : ℕ => chap9T 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9T
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

theorem hasDerivAt_chap9A_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun u => ∑' k : ℕ, chap9A u k) (∑' k : ℕ, chap9B y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9A_term n y)
    (fun n y hy => norm_chap9B_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9A_zero hy

theorem hasDerivAt_chap9S_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun u => ∑' k : ℕ, chap9S u k) (∑' k : ℕ, chap9Sderiv y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9S_term n y)
    (fun n y hy => norm_chap9Sderiv_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9S_zero hy

theorem hasDerivAt_chap9T_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun v => ∑' k : ℕ, chap9T v k) (∑' k : ℕ, chap9Tderiv y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9T_term n y)
    (fun n y hy => norm_chap9Tderiv_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9T_zero hy

theorem exists_rho_between {u : ℝ} (hu : |u| < 1) :
    ∃ ρ : ℝ, |u| < ρ ∧ ρ < 1 ∧ 0 < ρ ∧ u ∈ Set.Ioo (-ρ) ρ := by
  obtain ⟨ρ, h1, h2⟩ := exists_between hu
  have hρ0 : 0 < ρ := lt_of_le_of_lt (abs_nonneg u) h1
  have hmem : u ∈ Set.Ioo (-ρ) ρ := Set.mem_Ioo.mpr (abs_lt.mp h1)
  exact ⟨ρ, h1, h2, hρ0, hmem⟩

theorem hasDerivAt_chap9A {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9A w k) (∑' k : ℕ, chap9B u k) u := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hu
  exact hasDerivAt_chap9A_tsum_on_Ioo hρ0 hρ1 hmem

theorem hasDerivAt_chap9S {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9S w k) (∑' k : ℕ, chap9Sderiv u k) u := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hu
  exact hasDerivAt_chap9S_tsum_on_Ioo hρ0 hρ1 hmem

theorem hasDerivAt_chap9T {v : ℝ} (hv : |v| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9T w k) (∑' k : ℕ, chap9Tderiv v k) v := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hv
  exact hasDerivAt_chap9T_tsum_on_Ioo hρ0 hρ1 hmem

theorem chap9A_zero_tsum : (∑' k : ℕ, chap9A 0 k) = 0 := by
  have h : (fun k : ℕ => chap9A 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9A
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

theorem chap9A_eq_arcsin {u : ℝ} (hu : |u| < 1) :
    (∑' k : ℕ, chap9A u k) = Real.arcsin u := by
  have huIoo : u ∈ Set.Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr (abs_lt.mp hu)
  have h0Ioo : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h1ne : ∀ v : ℝ, v ∈ Set.Ioo (-1 : ℝ) 1 → v ≠ -1 ∧ v ≠ 1 := by
    intro v hv
    have h := Set.mem_Ioo.mp hv
    constructor <;> linarith
  have hderiv : ∀ v ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w) 0 v := by
    intro v hv
    have habs : |v| < 1 := abs_lt.mpr (Set.mem_Ioo.mp hv)
    have hA := hasDerivAt_chap9A habs
    rw [chap9B_tsum habs] at hA
    have hne := h1ne v hv
    have hArc := Real.hasDerivAt_arcsin hne.1 hne.2
    have hsub := hA.sub hArc
    rwa [sub_self] at hsub
  have hdiff : DifferentiableOn ℝ
      (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w) (Set.Ioo (-1) 1) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hEq : Set.EqOn (deriv (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w))
      0 (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    simp only [Pi.zero_apply]
    exact (hderiv x hx).deriv
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hEq
    huIoo h0Ioo
  have hf0 : (∑' k : ℕ, chap9A (0 : ℝ) k) - Real.arcsin 0 = 0 := by
    rw [chap9A_zero_tsum, Real.arcsin_zero, sub_self]
  have hfu : (∑' k : ℕ, chap9A u k) - Real.arcsin u
      = (∑' k : ℕ, chap9A (0 : ℝ) k) - Real.arcsin 0 := hconst
  linarith [hf0, hfu]

theorem summable_chap9Sderiv {u : ℝ} (hu : |u| < 1) :
    Summable (chap9Sderiv u) := by
  obtain ⟨ρ, h1, h2, hρ0, hmem⟩ := exists_rho_between hu
  exact Summable.of_norm_bounded (summable_rho_sq (le_of_lt hρ0) h2)
    (fun n => norm_chap9Sderiv_le (le_of_lt hρ0) hmem n)

theorem summable_chap9Tderiv {v : ℝ} (hv : |v| < 1) :
    Summable (chap9Tderiv v) := by
  obtain ⟨ρ, h1, h2, hρ0, hmem⟩ := exists_rho_between hv
  exact Summable.of_norm_bounded (summable_rho_sq (le_of_lt hρ0) h2)
    (fun n => norm_chap9Tderiv_le (le_of_lt hρ0) hmem n)

theorem mul_Sderiv_eq_A (u : ℝ) (k : ℕ) :
    u * chap9Sderiv u k = chap9A u k := by
  unfold chap9Sderiv chap9A
  have hpow : u ^ (2 * k + 1) = u ^ (2 * k) * u := by
    rw [pow_succ]
  rw [hpow]
  ring

theorem mul_Tderiv_eq_arctan_term (v : ℝ) (k : ℕ) :
    v * chap9Tderiv v k = (-1 : ℝ) ^ k * v ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ)) := by
  unfold chap9Tderiv
  have hpow : v ^ (2 * k + 1) = v ^ (2 * k) * v := by
    rw [pow_succ]
  rw [hpow]
  ring

theorem mul_tsum_Sderiv_eq_arcsin {u : ℝ} (hu : |u| < 1) :
    u * (∑' k : ℕ, chap9Sderiv u k) = Real.arcsin u := by
  have hsumm := summable_chap9Sderiv hu
  have hmul := hsumm.tsum_mul_left u
  have hEq : (fun k : ℕ => u * chap9Sderiv u k) = chap9A u := by
    funext k
    exact mul_Sderiv_eq_A u k
  have hA := chap9A_eq_arcsin hu
  calc u * (∑' k : ℕ, chap9Sderiv u k)
      = ∑' k : ℕ, u * chap9Sderiv u k := hmul.symm
    _ = ∑' k : ℕ, chap9A u k := by rw [hEq]
    _ = Real.arcsin u := hA

theorem mul_tsum_Tderiv_eq_arctan {v : ℝ} (hv : |v| < 1) :
    v * (∑' k : ℕ, chap9Tderiv v k) = Real.arctan v := by
  have hsumm := summable_chap9Tderiv hv
  have hmul := hsumm.tsum_mul_left v
  have hArc := Real.hasSum_arctan (x := v) (by rwa [Real.norm_eq_abs])
  have hEq : (fun k : ℕ => v * chap9Tderiv v k)
      = (fun n : ℕ => (-1 : ℝ) ^ n * v ^ (2 * n + 1) / (↑(2 * n + 1))) := by
    funext k
    exact mul_Tderiv_eq_arctan_term v k
  calc v * (∑' k : ℕ, chap9Tderiv v k)
      = ∑' k : ℕ, v * chap9Tderiv v k := hmul.symm
    _ = ∑' n : ℕ, (-1 : ℝ) ^ n * v ^ (2 * n + 1) / (↑(2 * n + 1)) := by rw [hEq]
    _ = Real.arctan v := hArc.tsum_eq

theorem cos_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.cos x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_pos : 0 < Real.cos x := cos_pos_aux (le_of_lt hx0) (le_of_lt hx)
  have hcos_lt : Real.cos x < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (le_of_lt (by linarith : x < Real.pi)) hx0
    rwa [Real.cos_zero] at h
  exact ⟨hcos_pos, hcos_lt⟩

theorem sin_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.sin x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hsin_lt : Real.sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith : -(Real.pi / 2) ≤ x)
      (le_refl (Real.pi / 2)) (by linarith : x < Real.pi / 2)
    rwa [Real.sin_pi_div_two] at h
  exact ⟨hsin_pos, hsin_lt⟩

theorem tan_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.tan x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_pos := (cos_mem_Ioo_of_mem hx0 hx).1
  have hsin_pos := (sin_mem_Ioo_of_mem hx0 hx).1
  have htan_pos : 0 < Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin_pos hcos_pos
  have hx_mem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hpi4_mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hlt : Real.tan x < Real.tan (Real.pi / 4) :=
    Real.strictMonoOn_tan hx_mem hpi4_mem hx
  rw [Real.tan_pi_div_four] at hlt
  exact ⟨htan_pos, hlt⟩

theorem abs_cos_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.cos x| < 1 := by
  have h := cos_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

theorem abs_sin_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.sin x| < 1 := by
  have h := sin_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

theorem abs_tan_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.tan x| < 1 := by
  have h := tan_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end

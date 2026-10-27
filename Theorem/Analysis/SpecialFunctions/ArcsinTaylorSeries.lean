/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Nat.Choose.Central
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace SpecialFunctions.ArcsinTaylorSeries

noncomputable section

theorem centralBinomial_div_pow_le_one (n : ℕ) :
    (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n) ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
  rw [div_le_one hpos]
  have h := Nat.choose_le_two_pow (2 * n) n
  have hcast : (Nat.choose (2 * n) n : ℝ) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  linarith

theorem summable_one_div_nat_add_one_sq :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    rw [Nat.cast_add, Nat.cast_one]
  rwa [hcongr]

theorem cast_two_mul_add_one (k : ℕ) :
    (((2 * k + 1 : ℕ)) : ℝ) = 2 * (k : ℝ) + 1 := by
  push_cast
  ring

theorem rawTerm_norm_le (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖(Nat.choose (2 * k) k : ℝ) * t ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  have hMpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  rw [norm_div, norm_mul, norm_mul]
  have hchoose : ‖(Nat.choose (2 * k) k : ℝ)‖ = (Nat.choose (2 * k) k : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have hpow2 : ‖((2 : ℝ) ^ (2 * k))‖ = (2 : ℝ) ^ (2 * k) :=
    abs_of_nonneg (by positivity)
  have hsq : ‖(((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ = ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
    abs_of_nonneg (by positivity)
  rw [hchoose, norm_pow, hpow2, hsq]
  have hc : (Nat.choose (2 * k) k : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h2pos : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    have h := centralBinomial_div_pow_le_one k
    rwa [div_le_one h2pos] at h
  have ht2 : ‖t‖ ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht
  have hnum : (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) ≤
      (2 : ℝ) ^ (2 * k) * 1 :=
    mul_le_mul hc ht2 (by positivity) (by positivity)
  have hbase : (((k : ℝ) + 1) ^ 2) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    rw [cast_two_mul_add_one]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hqpos : (0 : ℝ) < (((k : ℝ) + 1) ^ 2) := by positivity
  calc (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) /
          ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        ≤ ((2 : ℝ) ^ (2 * k) * 1) / ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) :=
          (div_le_div_iff_of_pos_right hDpos).mpr hnum
      _ = 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
          field_simp
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le hqpos hbase

end
end SpecialFunctions.ArcsinTaylorSeries

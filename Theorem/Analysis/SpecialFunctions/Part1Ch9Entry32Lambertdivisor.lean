/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem bCoeff32_pos (k : ℕ) : 0 < bCoeff32 k := by
  unfold bCoeff32
  positivity

theorem bCoeff32_succ (k : ℕ) :
    bCoeff32 (k + 1) = bCoeff32 k * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)) := by
  unfold bCoeff32
  have h1 : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have h2 : ((((2 * (k + 1)).factorial : ℕ)) : ℝ)
      = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((((2 * k).factorial : ℕ)) : ℝ) := by
    have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have e2 : 2 * k + 1 = (2 * k) + 1 := by omega
    conv_lhs => rw [e1]
    rw [Nat.factorial_succ]
    conv_lhs => rw [e2]
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [h1, h2]
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    ring
  rw [hpow]
  field_simp
  ring

theorem bCoeff32_one : bCoeff32 1 = 2 := by norm_num [bCoeff32, Nat.factorial]

theorem poly32_step (k : ℕ) (hk : 1 ≤ k) :
    16 * ((k : ℝ) + 1) ^ 7 ≤ (2 * (k : ℝ) + 1) ^ 4 * ((k : ℝ) + 2) ^ 3 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ)), sq_nonneg ((k : ℝ) ^ 2), sq_nonneg ((k : ℝ) ^ 3),
    mul_nonneg (show (0:ℝ) ≤ (k:ℝ) - 1 by linarith) (show (0:ℝ) ≤ (k:ℝ)^2 by positivity)]

theorem bCoeff32_pow4_le (k : ℕ) : (bCoeff32 k) ^ 4 ≤ 2 * ((k : ℝ) + 1) ^ 3 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => norm_num [bCoeff32]
    | 1 => rw [bCoeff32_one]; norm_num
    | (k + 2) =>
      have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
      have ih1 := ih (k + 1) (by omega)
      rw [bCoeff32_succ]
      have hstep : ((2 * (((k+1 : ℕ) : ℝ)+1) / (2*(((k+1 : ℕ) : ℝ))+1)) ^ 4)
          * (2 * ((((k+1 : ℕ) : ℝ))+1)^3) ≤ 2 * ((((k+1 : ℕ) : ℝ))+1+1)^3 := by
        have hpos4 : (0:ℝ) < (2*((((k+1:ℕ)):ℝ))+1)^4 := by positivity
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hpos4]
        have hpoly := poly32_step (k + 1) hk1
        have heq : ((((k+1 : ℕ)) : ℝ)+1+1) = ((((k+1 : ℕ)) : ℝ))+2 := by ring
        rw [heq]
        nlinarith [hpoly]
      calc (bCoeff32 (k + 1) * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1))) ^ 4
          = (bCoeff32 (k + 1)) ^ 4 * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4 := by ring
        _ ≤ (2 * (↑(k + 1) + 1) ^ 3) * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4 := by
            apply mul_le_mul_of_nonneg_right ih1 (by positivity)
        _ = ((2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4) * (2 * (↑(k + 1) + 1) ^ 3) := by ring
        _ ≤ 2 * (↑(k + 1) + 1 + 1) ^ 3 := hstep
        _ = 2 * ((((k + 2 : ℕ)) : ℝ) + 1) ^ 3 := by push_cast; ring

theorem rpow32_fourth (k : ℕ) :
    ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) ^ 4
      = 2 * ((k : ℝ) + 1) ^ 3 := by
  rw [mul_pow]
  have h1 : ((2 : ℝ) ^ ((1/4 : ℝ))) ^ (4:ℕ) = 2 := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by norm_num)]
    have he : (1/4 : ℝ) * ((4:ℕ) : ℝ) = 1 := by norm_num
    rw [he, Real.rpow_one]
  have h2 : ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) ^ (4:ℕ)) = ((k : ℝ) + 1) ^ (3:ℕ) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
    have he : (3/4 : ℝ) * ((4:ℕ) : ℝ) = ((3:ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
  rw [h1, h2]

theorem bCoeff32_le_rpow (k : ℕ) :
    bCoeff32 k ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by
  have h4 := bCoeff32_pow4_le k
  have hC4 := rpow32_fourth k
  have hle : (bCoeff32 k) ^ 4
      ≤ ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) ^ 4 := by
    rw [hC4]; exact h4
  have h0 : (0:ℝ) ≤ bCoeff32 k := le_of_lt (bCoeff32_pos k)
  have h1 : (0:ℝ) ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by positivity
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).mp hle

theorem summable32_maj54 :
    Summable (fun k : ℕ => ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) := by
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ ((5/4 : ℝ)))⁻¹)) :=
    (Real.summable_nat_rpow_inv).mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => ((((k + 1 : ℕ) : ℝ) ^ ((5/4 : ℝ)))⁻¹)) :=
    (summable_nat_add_iff (G := ℝ) 1).mpr hbase
  have heq : (fun k : ℕ => ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) =
      (fun k : ℕ => ((((k + 1 : ℕ) : ℝ) ^ ((5/4 : ℝ)))⁻¹)) := by
    funext k
    push_cast
    ring_nf
  rw [heq]
  exact hshift

theorem rpow32_div_eq (k : ℕ) :
    (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))
      = ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
  have hpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast _ 2, div_eq_mul_inv,
    ← Real.rpow_neg (le_of_lt hpos), ← Real.rpow_add hpos,
    show (3/4 : ℝ) + (-((2:ℕ) : ℝ)) = -((5/4) : ℝ) by norm_num,
    Real.rpow_neg (le_of_lt hpos)]

theorem cos32_pos (x : ℝ) (hx : |x| ≤ Real.pi / 4) : 0 < Real.cos x := by
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hneg : -(Real.pi / 4) ≤ x := neg_le_of_abs_le hx
    have hle : x ≤ Real.pi / 4 := le_of_abs_le hx
    have := Real.pi_pos
    constructor <;> linarith
  exact Real.cos_pos_of_mem_Ioo hmem

theorem tan32_abs_le (x : ℝ) (hx : |x| ≤ Real.pi / 4) : |Real.tan x| ≤ 1 := by
  have h1 : -(Real.pi / 4) ≤ x := neg_le_of_abs_le hx
  have h2 : x ≤ Real.pi / 4 := le_of_abs_le hx
  have hmem1 : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmemx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmono := Real.strictMonoOn_tan.monotoneOn
  have hle1 : Real.tan (-(Real.pi / 4)) ≤ Real.tan x :=
    hmono hmem1 hmemx (by simpa using h1)
  have hle2 : Real.tan x ≤ Real.tan (Real.pi / 4) :=
    hmono hmemx hmem2 (by simpa using h2)
  rw [Real.tan_pi_div_four] at hle2
  have hneg : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  rw [hneg] at hle1
  rw [abs_le]
  constructor <;> linarith

theorem summable32_maj2 :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff (G := ℝ) 1).mpr h2
  have heq : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    push_cast
    ring_nf
  rw [heq]
  exact hshift

theorem summable32_tan (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Summable (chapter9Entry19TanTerm x) := by
  have htan : |Real.tan x| ≤ 1 := tan32_abs_le x hx
  have hmaj := summable32_maj2
  have habs : Summable (fun k : ℕ => |chapter9Entry19TanTerm x k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
    unfold chapter9Entry19TanTerm
    rw [abs_div]
    have hpow : |(-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)| ≤ 1 := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact pow_le_one₀ (abs_nonneg _) htan
    calc |(-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)| / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)|
        ≤ 1 / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)| :=
          div_le_div_of_nonneg_right hpow (by positivity)
      _ = 1 / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [abs_of_nonneg (by positivity)]
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          have hle : ((k : ℝ) + 1) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
            have hkn : k + 1 ≤ 2 * k + 1 := by omega
            have h := Nat.cast_le (α := ℝ) |>.mpr hkn
            push_cast at h ⊢
            linarith
          calc ((k : ℝ) + 1) ^ 2 ≤ ((((2 * k + 1 : ℕ)) : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hle 2
            _ = ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by ring
  exact (summable_abs_iff).mp habs

theorem summable32_left (x : ℝ) : Summable (chapter9Entry32LeftTerm x) := by
  have hs : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
  have hCnn : (0:ℝ) ≤ (2 : ℝ) ^ ((1/4 : ℝ)) := by positivity
  have hMnn : ∀ k : ℕ, (0:ℝ) ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := fun k => by positivity
  have hmaj : Summable
      (fun k : ℕ => (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) :=
    summable32_maj54.mul_left _
  have habs : Summable (fun k : ℕ => |chapter9Entry32LeftTerm x k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
    have h1 : |bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)| ≤ bCoeff32 k := by
      rw [abs_mul]
      have hpow : |Real.sin (2 * x) ^ (2 * k + 1)| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hs
      calc |bCoeff32 k| * |Real.sin (2 * x) ^ (2 * k + 1)|
          = bCoeff32 k * |Real.sin (2 * x) ^ (2 * k + 1)| := by
            rw [abs_of_nonneg (le_of_lt (bCoeff32_pos k))]
        _ ≤ bCoeff32 k * 1 :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt (bCoeff32_pos k))
        _ = bCoeff32 k := mul_one _
    have hD2pos : (0:ℝ) < (((k : ℝ) + 1) ^ (2:ℕ)) := by positivity
    have hDle : (((k : ℝ) + 1) ^ (2:ℕ)) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ)) := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      push_cast at h ⊢
      linarith
    have hMdiv : (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ))
        ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ)) :=
      div_le_div_of_nonneg_left (hMnn k) hD2pos hDle
    have heq : chapter9Entry32LeftTerm x k
        = bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold chapter9Entry32LeftTerm bCoeff32
      field_simp
    rw [heq, abs_div]
    calc |bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)| / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)|
        ≤ bCoeff32 k / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)| :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = bCoeff32 k / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [abs_of_nonneg (by positivity)]
      _ ≤ ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
          div_le_div_of_nonneg_right (bCoeff32_le_rpow k) (by positivity)
      _ = (2 : ℝ) ^ ((1/4 : ℝ)) *
          ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / ((((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
          rw [mul_div_assoc]
      _ ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left hMdiv hCnn
      _ = (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
          rw [rpow32_div_eq]
  exact (summable_abs_iff).mp habs

theorem bCoeff32_zero : bCoeff32 0 = 1 := by
  norm_num [bCoeff32]

theorem bCoeff32_le_two_succ (k : ℕ) :
    bCoeff32 k ≤ 2 * ((k : ℝ) + 1) := by
  have h4 := bCoeff32_pow4_le k
  have hle : 2 * ((k : ℝ) + 1) ^ 3 ≤ (2 * ((k : ℝ) + 1)) ^ 4 := by
    have hk1 : (1:ℝ) ≤ (k : ℝ) + 1 := by
      have hkn : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have h8 : (1:ℝ) ≤ 8 * ((k : ℝ) + 1) := by linarith
    have hpos : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) ^ 3 := by positivity
    calc 2 * ((k : ℝ) + 1) ^ 3
        = 1 * (2 * ((k : ℝ) + 1) ^ 3) := by ring
      _ ≤ (8 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_right h8 hpos
      _ = (2 * ((k : ℝ) + 1)) ^ 4 := by ring
  have hB : (bCoeff32 k) ^ 4 ≤ (2 * ((k : ℝ) + 1)) ^ 4 := by
    linarith [h4, hle]
  have h0 : (0:ℝ) ≤ bCoeff32 k := le_of_lt (bCoeff32_pos k)
  have h1 : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).mp hB

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end

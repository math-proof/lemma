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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part7
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

theorem D32_zero : D32 0 = 0 := by
  unfold D32
  rw [H32_zero, A32_zero]
  ring

theorem continuousAt_D32_zero : ContinuousAt D32 0 := by
  have hH : ContinuousAt H32 0 := by
    have hmu : ContinuousAt mu32 0 := continuous_mu32.continuousAt
    have hS := continuousAt_S32_zero
    have hmul := hmu.mul hS
    have e : (mu32 * S32) = H32 := by
      funext z
      rfl
    rw [e] at hmul
    exact hmul
  have hA : ContinuousAt A32 0 := continuous_A32.continuousAt
  have hsub := hH.sub hA
  have e : (H32 - A32) = D32 := by
    funext z
    rfl
  rw [e] at hsub
  exact hsub

theorem hasDerivAt_D32_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt D32 0 z := by
  have hH := hasDerivAt_H32 hz0 hz1
  have hA := hasDerivAt_A32 hz0 hz1
  have hsub := hH.sub hA
  have e1 : (H32 - A32) = D32 := by
    funext y
    rfl
  rw [e1] at hsub
  have e2 : (1 / (2 * mu32 z)) - (1 / (2 * mu32 z)) = (0:ℝ) := by ring
  rw [e2] at hsub
  exact hsub

theorem S32_eq_of_mem {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    S32 z = A32 z / mu32 z := by
  have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (0:ℝ) 1) := isPreconnected_Ioo
  have hdiff : DifferentiableOn ℝ D32 (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioo.mp hx).1
    have hx1 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hHas := hasDerivAt_D32_zero hx0 hx1
    exact hHas.differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv D32) 0 (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioo.mp hx).1
    have hx1 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hHas := hasDerivAt_D32_zero hx0 hx1
    rw [hHas.deriv]
    rfl
  obtain ⟨C, hC⟩ :=
    hopen.exists_is_const_of_deriv_eq_zero hpre hdiff hderiv
  have hseq_mem : ∀ n : ℕ, (1:ℝ) / ((n : ℝ) + 2) ∈ Set.Ioo 0 1 := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    constructor
    · positivity
    · have h2 : (2:ℝ) ≤ (n : ℝ) + 2 := by linarith
      have hpos : (0:ℝ) < (n : ℝ) + 2 := by linarith
      calc (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
            apply one_div_le_one_div_of_le (by norm_num) h2
        _ < 1 := by norm_num
  have hseq_lim : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      tendsto_add_atTop_nat 1
    have hcomp := h1.comp hsucc
    have e : (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) ∘ (fun n : ℕ => n + 1)
        = fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2) := by
      funext n
      simp only [Function.comp_apply]
      push_cast
      ring
    rw [e] at hcomp
    exact hcomp
  have hDseq : ∀ n : ℕ, D32 ((1:ℝ) / ((n : ℝ) + 2)) = C := by
    intro n
    exact hC _ (hseq_mem n)
  have hcont := continuousAt_D32_zero
  have hlim : Tendsto (fun n : ℕ => D32 ((1:ℝ) / ((n : ℝ) + 2))) atTop
      (𝓝 (D32 0)) :=
    hcont.tendsto.comp hseq_lim
  rw [D32_zero] at hlim
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have hEq : (fun n : ℕ => D32 ((1:ℝ) / ((n : ℝ) + 2)))
      = fun _ : ℕ => C := by
    funext n
    exact hDseq n
  rw [hEq] at hlim
  have hC0 : C = 0 := tendsto_nhds_unique hconst hlim
  have hDz : D32 z = C := hC z (Set.mem_Ioo.mpr ⟨hz0, hz1⟩)
  rw [hC0] at hDz
  have hHA : H32 z = A32 z := by
    unfold D32 at hDz
    linarith [hDz]
  unfold H32 at hHA
  have hmuN := mu32_ne_zero hz0 hz1
  have hEq2 : S32 z = A32 z / mu32 z := by
    rw [eq_div_iff hmuN]
    linear_combination hHA
  exact hEq2

theorem S32_sq_eq {s : ℝ} (hs : ‖s‖ < 1) (hs0 : s ≠ 0) :
    S32 (s ^ 2) = Real.arcsin s / (s * √(1 - s ^ 2)) := by
  have hs0' : (0:ℝ) < s ^ 2 := sq_pos_of_ne_zero hs0
  have hs1 : s ^ 2 < 1 := by
    have habs : |s| < 1 := by
      rw [← Real.norm_eq_abs]
      exact hs
    have hmem := abs_lt.mp habs
    have hsq : s ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
    simpa using hsq
  have hEq := S32_eq_of_mem hs0' hs1
  have hA : A32 (s ^ 2) = Real.arcsin |s| := by
    unfold A32
    rw [Real.sqrt_sq_eq_abs]
  have hmu : mu32 (s ^ 2) = |s| * √(1 - s ^ 2) := by
    unfold mu32
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]
  rw [hEq, hA, hmu]
  have hsqrtN : √(1 - s ^ 2) ≠ 0 := by
    have hpos : (0:ℝ) < 1 - s ^ 2 := by linarith [hs1]
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have habsN : |s| ≠ 0 := abs_ne_zero.mpr hs0
  by_cases hsN : 0 ≤ s
  · have habs : |s| = s := abs_of_nonneg hsN
    rw [habs]
  · have hsneg : s < 0 := lt_of_not_ge hsN
    have habs : |s| = -s := abs_of_neg hsneg
    rw [habs, Real.arcsin_neg]
    field_simp

theorem deriv_F32_eq_S32 {s : ℝ} (hs : ‖s‖ < 1) :
    deriv F32 s = S32 (s ^ 2) := by
  have hHas := F32_hasDerivAt_of_norm_lt_one hs
  have hDeriv : deriv F32 s
      = ∑' k : ℕ, aCoeff32 k * s ^ (2 * k) :=
    hHas.deriv
  rw [hDeriv]
  have e : (fun k : ℕ => aCoeff32 k * s ^ (2 * k))
      = fun k : ℕ => aCoeff32 k * (s ^ 2) ^ k := by
    funext k
    rw [← pow_mul]
  rw [e]
  rfl

theorem G32_deriv_zero : (∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
    / (((2 * k + 1 : ℕ)) : ℝ)) = 1 := by
  have hsingle : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) 1 := by
    have h0 : (-1 : ℝ) ^ (0:ℕ) * (0:ℝ) ^ (2 * 0)
        / (((2 * 0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
    have h00 : ∀ b : ℕ, b ≠ 0 →
        (-1 : ℝ) ^ b * (0:ℝ) ^ (2 * b) / (((2 * b + 1 : ℕ)) : ℝ) = 0 := by
      intro b hb
      have hz : (0:ℝ) ^ (2 * b) = 0 := zero_pow (by omega)
      rw [hz]
      simp
    have hS := hasSum_single (0 : ℕ) h00
    rw [h0] at hS
    exact hS
  exact hsingle.tsum_eq

theorem G32_deriv_eq_arctan_div {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ))
      = Real.arctan t / t := by
  have hArctan := Real.hasSum_arctan ht
  have hDiv := hArctan.div_const t
  have hEq : (fun k : ℕ => (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ))
      = fun k : ℕ => ((-1 : ℝ) ^ k * t ^ (2 * k + 1)
        / (((2 * k + 1 : ℕ)) : ℝ)) / t := by
    funext k
    have hpow : t ^ (2 * k + 1) = t ^ (2 * k) * t := pow_succ t (2 * k)
    rw [hpow]
    field_simp
  rw [hEq]
  exact hDiv.tsum_eq

theorem deriv_G32_eq {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    deriv G32 t = Real.arctan t / t := by
  have hHas := G32_hasDerivAt_of_norm_lt_one ht
  have hDeriv : deriv G32 t
      = ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ) :=
    hHas.deriv
  rw [hDeriv]
  exact G32_deriv_eq_arctan_div ht ht0

theorem deriv_G32_zero : deriv G32 0 = 1 := by
  have h0 : ‖(0:ℝ)‖ < 1 := by norm_num
  have hHas := G32_hasDerivAt_of_norm_lt_one h0
  have hDeriv : deriv G32 0
      = ∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ) :=
    hHas.deriv
  rw [hDeriv]
  exact G32_deriv_zero

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end

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
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part5
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem seqU_mem_openLens (n : ℕ) : seqU n ∈ openLens := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht1 : seqT n < 1 := seqT_lt_one n
  have ht_half : seqT n ≤ 1 / 2 := seqT_le_half n
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : seqU n - 0 = seqU n := sub_zero _
    rw [hsub]
    unfold seqU
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  · rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖seqU n - 1‖ = 1 - seqT n := by
      have heq : seqU n - 1 = ((((seqT n - 1 : ℝ))) : ℂ) := by
        unfold seqU
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      have hneg : seqT n - 1 < 0 := by linarith
      rw [abs_of_neg hneg]
      ring
    rw [hnorm]
    linarith

theorem tendsto_seqU : Tendsto seqU atTop (𝓝 0) := by
  have h0 := tendsto_seqT
  have hcont := Complex.continuous_ofReal.tendsto (0 : ℝ)
  have hcomp : Tendsto (fun n : ℕ => (((seqT n : ℝ)) : ℂ)) atTop
      (𝓝 (((0 : ℝ)) : ℂ)) :=
    hcont.comp h0
  have hzero : (((0 : ℝ)) : ℂ) = (0 : ℂ) := Complex.ofReal_zero
  rw [hzero] at hcomp
  have hfun : seqU = (fun n : ℕ => (((seqT n : ℝ)) : ℂ)) := rfl
  rw [hfun]
  exact hcomp

theorem tendsto_one_sub_seqU : Tendsto (fun n : ℕ => (1 : ℂ) - seqU n)
    atTop (𝓝 1) := by
  have hU := tendsto_seqU
  have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  have hsub := h1.sub hU
  have hzero : (1 : ℂ) - 0 = 1 := sub_zero _
  rw [hzero] at hsub
  exact hsub

theorem seqU_mem_closedBall (n : ℕ) :
    seqU n ∈ Metric.closedBall (0 : ℂ) 1 :=
  Metric.ball_subset_closedBall (seqU_mem_openLens n).1

theorem one_sub_seqU_mem_closedBall (n : ℕ) :
    (1 : ℂ) - seqU n ∈ Metric.closedBall (0 : ℂ) 1 := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht1 : seqT n < 1 := seqT_lt_one n
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : ((1 : ℂ) - seqU n) - 0 = (1 : ℂ) - seqU n := sub_zero _
  rw [hsub]
  have heq : (1 : ℂ) - seqU n = ((((1 - seqT n : ℝ))) : ℂ) := by
    unfold seqU
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hpos : (0 : ℝ) < 1 - seqT n := by linarith
  rw [abs_of_pos hpos]
  linarith

theorem zero_mem_closedBall_one : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_self]
  norm_num

theorem one_mem_closedBall_one : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : (1 : ℂ) - 0 = 1 := sub_zero _
  rw [hsub, norm_one]

theorem tendsto_cLi2_seqU : Tendsto (fun n : ℕ => cLi2 (seqU n))
    atTop (𝓝 (cLi2 0)) := by
  have hcont : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) 0 :=
    continuousOn_cLi2.continuousWithinAt zero_mem_closedBall_one
  have hwithin : Tendsto seqU atTop (𝓝[Metric.closedBall (0 : ℂ) 1] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within seqU tendsto_seqU
      (Eventually.of_forall seqU_mem_closedBall)
  have hcomp : Tendsto (cLi2 ∘ seqU) atTop (𝓝 (cLi2 0)) :=
    hcont.tendsto.comp hwithin
  have hfun : (cLi2 ∘ seqU) = (fun n : ℕ => cLi2 (seqU n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

theorem tendsto_cLi2_one_sub_seqU : Tendsto (fun n : ℕ => cLi2 ((1 : ℂ) - seqU n))
    atTop (𝓝 (cLi2 1)) := by
  have hcont : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) 1 :=
    continuousOn_cLi2.continuousWithinAt one_mem_closedBall_one
  have hwithin : Tendsto (fun n : ℕ => (1 : ℂ) - seqU n) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_sub_seqU (Eventually.of_forall one_sub_seqU_mem_closedBall)
  have hcomp : Tendsto (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - seqU n)) atTop
      (𝓝 (cLi2 1)) :=
    hcont.tendsto.comp hwithin
  have hfun : (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - seqU n))
      = (fun n : ℕ => cLi2 ((1 : ℂ) - seqU n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

theorem abs_log_one_sub_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    |Real.log (1 - t)| ≤ 2 * t := by
  have hu_pos : (0 : ℝ) < 1 - t := by linarith
  have h1 : Real.log (1 - t) ≤ (1 - t) - 1 :=
    Real.log_le_sub_one_of_pos hu_pos
  have h2 : 1 - (1 - t)⁻¹ ≤ Real.log (1 - t) :=
    Real.one_sub_inv_le_log_of_pos hu_pos
  have hlog_nonpos : Real.log (1 - t) ≤ 0 := by linarith
  have habs : |Real.log (1 - t)| = -Real.log (1 - t) :=
    abs_of_nonpos hlog_nonpos
  rw [habs]
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp
    ring
  have hle : -Real.log (1 - t) ≤ t / (1 - t) := by
    have h2' : -Real.log (1 - t) ≤ (1 - t)⁻¹ - 1 := by linarith
    rw [heq] at h2'
    exact h2'
  have hdiv : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ hu_pos]
    have ht_nonneg : (0 : ℝ) ≤ t := le_of_lt ht0
    nlinarith [ht_nonneg, ht1, hu_pos]
  exact le_trans hle hdiv

theorem tendsto_mul_log_seqT :
    Tendsto (fun n : ℕ => seqT n * Real.log (seqT n)) atTop (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ => x * Real.log x) :=
    Real.continuous_mul_log
  have hcomp : Tendsto ((fun x : ℝ => x * Real.log x) ∘ seqT) atTop
      (𝓝 ((0 : ℝ) * Real.log 0)) :=
    (hcont.tendsto 0).comp tendsto_seqT
  have h0val : (0 : ℝ) * Real.log 0 = 0 := zero_mul _
  rw [h0val] at hcomp
  have hfun : ((fun x : ℝ => x * Real.log x) ∘ seqT)
      = (fun n : ℕ => seqT n * Real.log (seqT n)) := rfl
  rw [hfun] at hcomp
  exact hcomp

theorem tendsto_log_prod_seqU :
    Tendsto (fun n : ℕ => Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))
      atTop (𝓝 0) := by
  have hbound : ∀ n : ℕ,
      ‖Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n)‖
        ≤ 2 * |seqT n * Real.log (seqT n)| := by
    intro n
    have ht0 : 0 < seqT n := seqT_pos n
    have ht1 : seqT n ≤ 1 / 2 := seqT_le_half n
    have hlog1 : Complex.log (seqU n) = (((Real.log (seqT n) : ℝ)) : ℂ) := by
      have h := Complex.ofReal_log (le_of_lt ht0)
      unfold seqU at *
      rw [← h]
    have heq2 : (1 : ℂ) - seqU n = ((((1 - seqT n : ℝ))) : ℂ) := by
      unfold seqU
      push_cast
      ring
    have h1t : (0 : ℝ) ≤ 1 - seqT n := by linarith [seqT_lt_one n]
    have hlog2 : Complex.log ((1 : ℂ) - seqU n)
        = (((Real.log (1 - seqT n) : ℝ)) : ℂ) := by
      rw [heq2, ← Complex.ofReal_log h1t]
    rw [hlog1, hlog2, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_mul]
    have hblog := abs_log_one_sub_le ht0 ht1
    have ht_abs : |seqT n| = seqT n := abs_of_pos ht0
    have hmul_abs : |seqT n * Real.log (seqT n)|
        = seqT n * |Real.log (seqT n)| := by
      rw [abs_mul, ht_abs]
    rw [hmul_abs]
    calc |Real.log (seqT n)| * |Real.log (1 - seqT n)|
        ≤ |Real.log (seqT n)| * (2 * seqT n) := by
          apply mul_le_mul_of_nonneg_left hblog (abs_nonneg _)
      _ = 2 * (seqT n * |Real.log (seqT n)|) := by ring
  have hbase := tendsto_mul_log_seqT
  have habs : Tendsto (fun n : ℕ => |seqT n * Real.log (seqT n)|) atTop (𝓝 0) := by
    have h := hbase.abs
    simpa using h
  have h2 : Tendsto (fun n : ℕ => 2 * |seqT n * Real.log (seqT n)|) atTop
      (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have hmul := hconst.mul habs
    have h20 : (2 : ℝ) * 0 = 0 := mul_zero _
    rw [h20] at hmul
    exact hmul
  exact squeeze_zero_norm' (Eventually.of_forall hbound) h2

theorem tendsto_spenceFun_seqU :
    Tendsto (fun n : ℕ => spenceFun (seqU n)) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
  have h1 := tendsto_cLi2_seqU
  have h2 := tendsto_cLi2_one_sub_seqU
  have h3 := tendsto_log_prod_seqU
  have hadd := h1.add h2
  have hall := hadd.add h3
  have h0eq : cLi2 (0 : ℂ) = 0 := cLi2_zero
  have h1eq : cLi2 (1 : ℂ) = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := cLi2_one
  rw [h0eq, h1eq] at hall
  have hval : ((0 : ℂ) + (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) + (0 : ℂ)
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
    simp
  rw [hval] at hall
  have hfun : (fun n : ℕ => spenceFun (seqU n))
      = (fun n : ℕ => (cLi2 (seqU n) + cLi2 ((1 : ℂ) - seqU n)
        + Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))) := rfl
  rw [hfun]
  have hall2 : Tendsto (fun n : ℕ => (cLi2 (seqU n) + cLi2 ((1 : ℂ) - seqU n)
      + Complex.log (seqU n) * Complex.log ((1 : ℂ) - seqU n))) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := hall
  exact hall2

theorem spenceFun_eq_pi_sq_on_openLens :
    ∀ z ∈ openLens, spenceFun z = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  obtain ⟨C, hC⟩ := spenceFun_const_on_openLens
  have hlim := tendsto_spenceFun_seqU
  have hfun : (fun n : ℕ => spenceFun (seqU n)) = fun _ => C := by
    funext n
    exact hC _ (seqU_mem_openLens n)
  have hconst : Tendsto (fun n : ℕ => spenceFun (seqU n)) atTop (𝓝 C) := by
    rw [hfun]
    exact tendsto_const_nhds
  have hCEq : C = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) :=
    tendsto_nhds_unique hconst hlim
  intro z hz
  rw [hC z hz, hCEq]

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end

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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part7
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

theorem blendSeq_mem_openLens {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : blendSeq z0 n ∈ openLens := by
  have ht0 : 0 < seqT n := seqT_pos n
  have ht_half : seqT n ≤ 1 / 2 := seqT_le_half n
  have h1t_nonneg : (0 : ℝ) ≤ 1 - seqT n := by
    have ht1 : seqT n < 1 := seqT_lt_one n
    linarith
  have hz0 : ‖z0‖ ≤ 1 := norm_le_one_of_mem_closedLens hz
  have hz1 : ‖(1 : ℂ) - z0‖ ≤ 1 := norm_one_sub_le_one_of_mem_closedLens hz
  have hn1 : ‖((((1 - seqT n : ℝ))) : ℂ)‖ = 1 - seqT n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1t_nonneg]
  have hn2 : ‖((((seqT n / 2 : ℝ))) : ℂ)‖ = seqT n / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) ≤ seqT n / 2 := by positivity
    rw [abs_of_nonneg hpos]
  have hblend : ∀ (w : ℂ) (_ : ‖w‖ ≤ 1),
      ‖((((1 - seqT n : ℝ))) : ℂ) * w + ((((seqT n / 2 : ℝ))) : ℂ)‖ < 1 := by
    intro w hw
    calc ‖((((1 - seqT n : ℝ))) : ℂ) * w + ((((seqT n / 2 : ℝ))) : ℂ)‖
        ≤ ‖((((1 - seqT n : ℝ))) : ℂ) * w‖
          + ‖((((seqT n / 2 : ℝ))) : ℂ)‖ := norm_add_le _ _
      _ = (1 - seqT n) * ‖w‖ + seqT n / 2 := by
          rw [norm_mul, hn1, hn2]
      _ ≤ (1 - seqT n) * 1 + seqT n / 2 := by
          have hmul : (1 - seqT n) * ‖w‖ ≤ (1 - seqT n) * 1 :=
            mul_le_mul_of_nonneg_left hw h1t_nonneg
          linarith
      _ < 1 := by linarith
  have hw0 : ‖blendSeq z0 n‖ < 1 := by
    unfold blendSeq
    exact hblend z0 hz0
  have heq1 : (1 : ℂ) - blendSeq z0 n
      = (((1 - seqT n : ℝ)) : ℂ) * ((1 : ℂ) - z0)
        + ((((seqT n / 2 : ℝ))) : ℂ) := by
    unfold blendSeq
    have hab : ((((1 - seqT n : ℝ))) : ℂ)
        + 2 * (((seqT n / 2 : ℝ)) : ℂ) = 1 := by
      have hreal : (1 - seqT n) + 2 * (seqT n / 2) = (1 : ℝ) := by ring
      have hcast : ((((1 - seqT n) + 2 * (seqT n / 2) : ℝ)) : ℂ)
          = (((1 : ℝ)) : ℂ) := by rw [hreal]
      have hexpand : ((((1 - seqT n) + 2 * (seqT n / 2) : ℝ)) : ℂ)
          = ((((1 - seqT n : ℝ))) : ℂ)
            + 2 * (((seqT n / 2 : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hexpand] at hcast
      simpa using hcast
    have hring : ∀ (a b z0 : ℂ), a + 2 * b = 1 →
        (1 - (a * z0 + b) = a * (1 - z0) + b) := by
      intro a b z0 hab2
      linear_combination -hab2
    exact hring _ _ _ hab
  have hw1 : ‖(1 : ℂ) - blendSeq z0 n‖ < 1 := by
    rw [heq1]
    exact hblend ((1 : ℂ) - z0) hz1
  constructor
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : blendSeq z0 n - 0 = blendSeq z0 n := sub_zero _
    rw [hsub]
    exact hw0
  · rw [Metric.mem_ball, dist_eq_norm]
    have hrev : ‖blendSeq z0 n - 1‖ = ‖(1 : ℂ) - blendSeq z0 n‖ :=
      norm_sub_rev _ _
    rw [hrev]
    exact hw1

theorem tendsto_blendSeq (z0 : ℂ) :
    Tendsto (blendSeq z0) atTop (𝓝 z0) := by
  have hmul : Tendsto (fun n : ℕ => seqU n * ((1 / 2 : ℂ) - z0)) atTop (𝓝 0) := by
    have h1 := tendsto_seqU
    have h2 : Tendsto (fun _ : ℕ => ((1 / 2 : ℂ) - z0)) atTop
        (𝓝 ((1 / 2 : ℂ) - z0)) := tendsto_const_nhds
    have hprod := h1.mul h2
    have h00 : (0 : ℂ) * ((1 / 2 : ℂ) - z0) = 0 := zero_mul _
    rw [h00] at hprod
    exact hprod
  have hadd : Tendsto (fun n : ℕ => z0 + seqU n * ((1 / 2 : ℂ) - z0)) atTop
      (𝓝 z0) := by
    have h1 : Tendsto (fun _ : ℕ => z0) atTop (𝓝 z0) := tendsto_const_nhds
    have hsum := h1.add hmul
    have hzz : z0 + (0 : ℂ) = z0 := add_zero _
    rw [hzz] at hsum
    exact hsum
  have hfun : blendSeq z0
      = (fun n : ℕ => z0 + seqU n * ((1 / 2 : ℂ) - z0)) := by
    funext n
    unfold blendSeq seqU
    push_cast
    ring
  rw [hfun]
  exact hadd

theorem tendsto_one_sub_blendSeq (z0 : ℂ) :
    Tendsto (fun n : ℕ => (1 : ℂ) - blendSeq z0 n) atTop
      (𝓝 ((1 : ℂ) - z0)) := by
  have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
  exact h1.sub (tendsto_blendSeq z0)

theorem blendSeq_mem_closedBall {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : blendSeq z0 n ∈ Metric.closedBall (0 : ℂ) 1 :=
  Metric.ball_subset_closedBall (blendSeq_mem_openLens hz n).1

theorem one_sub_blendSeq_mem_closedBall {z0 : ℂ} (hz : z0 ∈ closedLens)
    (n : ℕ) : (1 : ℂ) - blendSeq z0 n ∈ Metric.closedBall (0 : ℂ) 1 := by
  have hmem := blendSeq_mem_openLens hz n
  have h1 : blendSeq z0 n ∈ Metric.ball (1 : ℂ) 1 := hmem.2
  have hdist : dist (blendSeq z0 n) (1 : ℂ) < 1 := Metric.mem_ball.mp h1
  rw [dist_eq_norm] at hdist
  have hnorm : ‖(1 : ℂ) - blendSeq z0 n‖ ≤ 1 := by
    have hrev : ‖(1 : ℂ) - blendSeq z0 n‖ = ‖blendSeq z0 n - 1‖ :=
      norm_sub_rev _ _
    rw [hrev]
    exact le_of_lt hdist
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : ((1 : ℂ) - blendSeq z0 n) - 0 = (1 : ℂ) - blendSeq z0 n :=
    sub_zero _
  rw [hsub]
  exact hnorm

theorem spenceFun_eq_pi_sq_on_closedLens {z0 : ℂ} (hz : z0 ∈ closedLens)
    (hz0ne : z0 ≠ 0) (hz1ne : (1 : ℂ) - z0 ≠ 0) :
    spenceFun z0 = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
  have hz0Ball : z0 ∈ Metric.closedBall (0 : ℂ) 1 := hz.1
  have hz1Ball : (1 : ℂ) - z0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hle : ‖(1 : ℂ) - z0‖ ≤ 1 := norm_one_sub_le_one_of_mem_closedLens hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : ((1 : ℂ) - z0) - 0 = (1 : ℂ) - z0 := sub_zero _
    rw [hsub]
    exact hle
  have hcont0 : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1) z0 :=
    continuousOn_cLi2.continuousWithinAt hz0Ball
  have hcont1 : ContinuousWithinAt cLi2 (Metric.closedBall (0 : ℂ) 1)
      ((1 : ℂ) - z0) :=
    continuousOn_cLi2.continuousWithinAt hz1Ball
  have hblend_within : Tendsto (blendSeq z0) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] z0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_blendSeq z0)
      (Eventually.of_forall (blendSeq_mem_closedBall hz))
  have h1blend_within : Tendsto (fun n : ℕ => (1 : ℂ) - blendSeq z0 n) atTop
      (𝓝[Metric.closedBall (0 : ℂ) 1] ((1 : ℂ) - z0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_one_sub_blendSeq z0)
      (Eventually.of_forall (one_sub_blendSeq_mem_closedBall hz))
  have hL0 : Tendsto (fun n : ℕ => cLi2 (blendSeq z0 n)) atTop
      (𝓝 (cLi2 z0)) := by
    have hcomp : Tendsto (cLi2 ∘ blendSeq z0) atTop (𝓝 (cLi2 z0)) :=
      hcont0.tendsto.comp hblend_within
    have hfun : (cLi2 ∘ blendSeq z0)
        = (fun n : ℕ => cLi2 (blendSeq z0 n)) := rfl
    rw [hfun] at hcomp
    exact hcomp
  have hL1 : Tendsto (fun n : ℕ => cLi2 ((1 : ℂ) - blendSeq z0 n)) atTop
      (𝓝 (cLi2 ((1 : ℂ) - z0))) := by
    have hcomp : Tendsto (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - blendSeq z0 n)) atTop
        (𝓝 (cLi2 ((1 : ℂ) - z0))) :=
      hcont1.tendsto.comp h1blend_within
    have hfun : (cLi2 ∘ (fun n : ℕ => (1 : ℂ) - blendSeq z0 n))
        = (fun n : ℕ => cLi2 ((1 : ℂ) - blendSeq z0 n)) := rfl
    rw [hfun] at hcomp
    exact hcomp
  have hslit0 : z0 ∈ Complex.slitPlane :=
    mem_slitPlane_of_mem_closedLens hz hz0ne
  have hslit1 : (1 : ℂ) - z0 ∈ Complex.slitPlane :=
    one_sub_mem_slitPlane_of_mem_closedLens hz hz1ne
  have hlog0 : Tendsto (fun n : ℕ => Complex.log (blendSeq z0 n)) atTop
      (𝓝 (Complex.log z0)) :=
    (tendsto_blendSeq z0).clog hslit0
  have hlog1 : Tendsto (fun n : ℕ => Complex.log ((1 : ℂ) - blendSeq z0 n))
      atTop (𝓝 (Complex.log ((1 : ℂ) - z0))) :=
    (tendsto_one_sub_blendSeq z0).clog hslit1
  have hprod : Tendsto (fun n : ℕ => Complex.log (blendSeq z0 n)
      * Complex.log ((1 : ℂ) - blendSeq z0 n)) atTop
      (𝓝 (Complex.log z0 * Complex.log ((1 : ℂ) - z0))) :=
    hlog0.mul hlog1
  have hlim : Tendsto (fun n : ℕ => spenceFun (blendSeq z0 n)) atTop
      (𝓝 (spenceFun z0)) := by
    have hadd := hL0.add hL1
    have hall := hadd.add hprod
    have hfun : (fun n : ℕ => spenceFun (blendSeq z0 n))
        = (fun n : ℕ => (cLi2 (blendSeq z0 n)
          + cLi2 ((1 : ℂ) - blendSeq z0 n)
          + Complex.log (blendSeq z0 n)
            * Complex.log ((1 : ℂ) - blendSeq z0 n))) := rfl
    have hval : spenceFun z0
        = (cLi2 z0 + cLi2 ((1 : ℂ) - z0)
          + Complex.log z0 * Complex.log ((1 : ℂ) - z0)) := rfl
    rw [hfun, hval]
    exact hall
  have hfunC : (fun n : ℕ => spenceFun (blendSeq z0 n))
      = fun _ => (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by
    funext n
    exact spenceFun_eq_pi_sq_on_openLens _ (blendSeq_mem_openLens hz n)
  have hconst : Tendsto (fun n : ℕ => spenceFun (blendSeq z0 n)) atTop
      (𝓝 (((Real.pi ^ 2 / 6 : ℝ)) : ℂ)) := by
    rw [hfunC]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim hconst

theorem spence_identity {z w : ℂ} (hzw : z + w = 1)
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hz0 : z ≠ 0) (hw0 : w ≠ 0) :
    cLi2 z + cLi2 w
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) - Complex.log z * Complex.log w := by
  have h1z : w = (1 : ℂ) - z := by linear_combination hzw
  have hzBall : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z - 0 = z := sub_zero _
    rw [hsub]
    exact hz
  have hwBall : z ∈ Metric.closedBall (1 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : z - 1 = -w := by linear_combination hzw
    rw [heq, norm_neg]
    exact hw
  have hzLens : z ∈ closedLens := ⟨hzBall, hwBall⟩
  have h1ne : (1 : ℂ) - z ≠ 0 := h1z ▸ hw0
  have hsp := spenceFun_eq_pi_sq_on_closedLens hzLens hz0 h1ne
  have hsp2 : cLi2 z + cLi2 ((1 : ℂ) - z)
      + Complex.log z * Complex.log ((1 : ℂ) - z)
      = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := hsp
  rw [← h1z] at hsp2
  linear_combination hsp2

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry24_dougall`.
-/
theorem ramanujan_part1_ch9_entry24_dougall (x y theta phi : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (htheta : -Real.pi < theta ∧ theta ≤ Real.pi)
    (hphi : -Real.pi < phi ∧ phi ≤ Real.pi)
    (hxy : (x : ℂ) * Complex.exp (Complex.I * theta) +
      (y : ℂ) * Complex.exp (Complex.I * phi) = 1) :
    Summable (chapter9DilogCosTerm x theta) ∧
      Summable (chapter9DilogCosTerm y phi) ∧
      Summable (chapter9DilogSinTerm x theta) ∧
      Summable (chapter9DilogSinTerm y phi) ∧
      (∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.pi ^ 2 / 6 - chapter9BoundaryLog x * chapter9BoundaryLog y +
          theta * phi ∧
      (∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -phi * chapter9BoundaryLog x - theta * chapter9BoundaryLog y := by
  have hcosx := summable_dilogCosTerm x theta hx.1 hx.2
  have hcosy := summable_dilogCosTerm y phi hy.1 hy.2
  have hsinx := summable_dilogSinTerm x theta hx.1 hx.2
  have hsiny := summable_dilogSinTerm y phi hy.1 hy.2
  have key : ((∑' j : ℕ, chapter9DilogCosTerm x theta j) +
          ∑' j : ℕ, chapter9DilogCosTerm y phi j =
        Real.pi ^ 2 / 6 - chapter9BoundaryLog x * chapter9BoundaryLog y +
          theta * phi) ∧
      ((∑' j : ℕ, chapter9DilogSinTerm x theta j) +
          ∑' j : ℕ, chapter9DilogSinTerm y phi j =
        -phi * chapter9BoundaryLog x - theta * chapter9BoundaryLog y) := by
    by_cases hx0 : x = 0
    · subst hx0
      simp only [Complex.ofReal_zero, zero_mul, zero_add] at hxy
      obtain ⟨hy1, hphi0⟩ := edge_of_rho_zero hy hphi hxy
      subst hy1
      subst hphi0
      constructor
      · rw [tsum_dilogCos_zero, zero_add, hasSum_dilogCos_one_zero.tsum_eq,
          boundaryLog_zero, boundaryLog_one]
        simp
      · rw [tsum_dilogSin_zero, tsum_dilogSin_one_zero, boundaryLog_zero,
          boundaryLog_one]
        simp
    · by_cases hy0 : y = 0
      · subst hy0
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at hxy
        obtain ⟨hx1, htheta0⟩ := edge_of_rho_zero hx htheta hxy
        subst hx1
        subst htheta0
        constructor
        · rw [hasSum_dilogCos_one_zero.tsum_eq, tsum_dilogCos_zero, add_zero,
            boundaryLog_one, boundaryLog_zero]
          simp
        · rw [tsum_dilogSin_one_zero, tsum_dilogSin_zero, boundaryLog_one,
            boundaryLog_zero]
          simp
      · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
        have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
        have hznorm : ‖((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))‖ ≤ 1 := by
          rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hx.1]
          exact hx.2
        have hwnorm : ‖((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))‖ ≤ 1 := by
          rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hy.1]
          exact hy.2
        have hXsumm := summable_cLi2
          (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) hznorm
        have hYsumm := summable_cLi2
          (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) hwnorm
        have hXre : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).re
            = ∑' j : ℕ, chapter9DilogCosTerm x theta j := by
          rw [Complex.re_tsum hXsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_cos x theta j
        have hYre : (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).re
            = ∑' j : ℕ, chapter9DilogCosTerm y phi j := by
          rw [Complex.re_tsum hYsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_cos y phi j
        have hXim : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).im
            = ∑' j : ℕ, chapter9DilogSinTerm x theta j := by
          rw [Complex.im_tsum hXsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_sin x theta j
        have hYim : (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
            ((((j + 1 : ℕ)) : ℂ) ^ 2)).im
            = ∑' j : ℕ, chapter9DilogSinTerm y phi j := by
          rw [Complex.im_tsum hYsumm]
          refine tsum_congr fun j => ?_
          exact cLi2_sin y phi j
        have hlogx : Complex.log (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))
            = (((Real.log x : ℝ)) : ℂ) + ((theta : ℝ) : ℂ) * Complex.I :=
          log_ofReal_mul_exp_I x theta hxpos ⟨htheta.1, htheta.2⟩
        have hlogy : Complex.log (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ)))
            = (((Real.log y : ℝ)) : ℂ) + ((phi : ℝ) : ℂ) * Complex.I :=
          log_ofReal_mul_exp_I y phi hypos ⟨hphi.1, hphi.2⟩
        have hBlogx : chapter9BoundaryLog x = Real.log x := by
          simp [chapter9BoundaryLog, hx0]
        have hBlogy : chapter9BoundaryLog y = Real.log y := by
          simp [chapter9BoundaryLog, hy0]
        have hz0 : (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ≠ 0 := by
          have hnorm_eq : ‖(((x : ℝ) : ℂ)
              * Complex.exp (Complex.I * (theta : ℂ)))‖ = x := by
            rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hx.1]
          have hpos : (0 : ℝ) < ‖(((x : ℝ) : ℂ)
              * Complex.exp (Complex.I * (theta : ℂ)))‖ := by
            rw [hnorm_eq]
            exact hxpos
          exact norm_ne_zero_iff.mp (ne_of_gt hpos)
        have hw0 : (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ≠ 0 := by
          have hnorm_eq : ‖(((y : ℝ) : ℂ)
              * Complex.exp (Complex.I * (phi : ℂ)))‖ = y := by
            rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hy.1]
          have hpos : (0 : ℝ) < ‖(((y : ℝ) : ℂ)
              * Complex.exp (Complex.I * (phi : ℂ)))‖ := by
            rw [hnorm_eq]
            exact hypos
          exact norm_ne_zero_iff.mp (ne_of_gt hpos)
        have hzw : (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ)))
            + (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) = 1 := hxy
        have hsp := spence_identity hzw hznorm hwnorm hz0 hw0
        have spence : (∑' j : ℕ, (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) ^ (j + 1) /
              ((((j + 1 : ℕ)) : ℂ) ^ 2)) +
            (∑' j : ℕ, (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) ^ (j + 1) /
              ((((j + 1 : ℕ)) : ℂ) ^ 2))
            = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) -
              Complex.log (((x : ℝ) : ℂ) * Complex.exp (Complex.I * (theta : ℂ))) *
              Complex.log (((y : ℝ) : ℂ) * Complex.exp (Complex.I * (phi : ℂ))) :=
          hsp
        have hre := congrArg Complex.re spence
        have him := congrArg Complex.im spence
        rw [Complex.add_re, hXre, hYre, hlogx, hlogy] at hre
        rw [Complex.add_im, hXim, hYim, hlogx, hlogy] at him
        simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_re,
          Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, sub_zero, add_zero, zero_add] at hre
        simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_im,
          Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_one, mul_zero, add_zero, zero_add] at him
        rw [hBlogx, hBlogy]
        constructor
        · linarith [hre]
        · linarith [him]
  exact ⟨hcosx, hcosy, hsinx, hsiny, key.1, key.2⟩

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end

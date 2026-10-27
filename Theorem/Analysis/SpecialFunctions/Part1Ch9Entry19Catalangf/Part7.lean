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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part7
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

theorem hasDerivAt_chap9f {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt chap9f (-Real.log (Real.sin θ)) θ := by
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt (sin_mem_Ioo_pi_half h0 h1).1
  have hE := hasDerivAt_chap9E h0 h1
  have hlog : HasDerivAt (fun θ : ℝ => Real.log (Real.sin θ))
      (Real.cos θ / Real.sin θ) θ :=
    (Real.hasDerivAt_sin θ).log hsin_ne
  have hid : HasDerivAt (fun θ : ℝ => θ) 1 θ := hasDerivAt_id' θ
  have hmul : HasDerivAt (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (1 * Real.log (Real.sin θ) + θ * (Real.cos θ / Real.sin θ)) θ :=
    hid.mul hlog
  have hsub := hE.sub hmul
  have hval : θ * Real.cos θ / Real.sin θ
      - (1 * Real.log (Real.sin θ) + θ * (Real.cos θ / Real.sin θ))
      = -Real.log (Real.sin θ) := by
    ring
  rw [hval] at hsub
  exact hsub

theorem sin_mem_Icc_pi_half {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  have hle : Real.sin θ ≤ 1 := Real.sin_le_one θ
  constructor <;> linarith

theorem continuousOn_chap9E :
    ContinuousOn chap9E (Set.Icc 0 (Real.pi / 2)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_sin.continuousOn
    (fun θ hθ => sin_mem_Icc_pi_half (Set.mem_Icc.mp hθ).1 (Set.mem_Icc.mp hθ).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.sin = chap9E := rfl
  rwa [hEq] at hcomp

theorem tendsto_lower_zero :
    Tendsto (fun θ : ℝ => -(θ * Real.log (2 / Real.pi * θ)))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hphi : Tendsto (fun θ : ℝ => 2 / Real.pi * θ)
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
    have hcont : Continuous (fun θ : ℝ => 2 / Real.pi * θ) :=
      continuous_const.mul continuous_id
    have h := hcont.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hbase : Tendsto (fun x : ℝ => x * Real.log x)
      (nhds 0) (nhds 0) := by
    simpa using Real.continuous_mul_log.tendsto 0
  have hcomp : Tendsto (fun θ : ℝ => (2 / Real.pi * θ) * Real.log (2 / Real.pi * θ))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) :=
    hbase.comp hphi
  have hEq : (fun θ : ℝ => -(θ * Real.log (2 / Real.pi * θ)))
      = (fun θ : ℝ => (-(Real.pi / 2)) * ((2 / Real.pi * θ) * Real.log (2 / Real.pi * θ))) := by
    funext θ
    field_simp
  rw [hEq]
  have hmul := hcomp.const_mul (-(Real.pi / 2))
  simpa using hmul

theorem tendsto_neg_mul_log_sin_zero :
    Tendsto (fun θ : ℝ => -(θ * Real.log (Real.sin θ)))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_lower_zero
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hlog : Real.log (Real.sin θ) ≤ 0 := Real.log_nonpos hsin_nn hsin_le
    have hmul : θ * Real.log (Real.sin θ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h0 hlog
    linarith
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    by_cases hθ0 : θ = 0
    · rw [hθ0]
      simp
    · have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
      have hlow_pos : 0 < 2 / Real.pi * θ := by positivity
      have hle : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin h0 h1
      have hlog_le : Real.log (2 / Real.pi * θ) ≤ Real.log (Real.sin θ) :=
        Real.log_le_log hlow_pos hle
      have hmul_le : θ * Real.log (2 / Real.pi * θ) ≤ θ * Real.log (Real.sin θ) :=
        mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpos)
      linarith

theorem tendsto_mul_log_sin_zero :
    Tendsto (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  simpa using tendsto_neg_mul_log_sin_zero.neg

theorem continuousOn_mul_log_sin :
    ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  intro θ hθ
  by_cases hθ0 : θ = 0
  · rw [hθ0]
    have hval : (0 : ℝ) * Real.log (Real.sin 0) = 0 := by simp
    rw [ContinuousWithinAt, hval]
    exact tendsto_mul_log_sin_zero
  · have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
    have hsin_ne : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith))
    have hlog : ContinuousAt (fun θ : ℝ => Real.log (Real.sin θ)) θ :=
      (Real.continuousAt_log hsin_ne).comp Real.continuous_sin.continuousAt
    have hmul : ContinuousAt (fun θ : ℝ => θ * Real.log (Real.sin θ)) θ :=
      continuous_id.continuousAt.mul hlog
    exact hmul.continuousWithinAt

theorem continuousOn_chap9f :
    ContinuousOn chap9f (Set.Icc 0 (Real.pi / 2)) :=
  continuousOn_chap9E.sub continuousOn_mul_log_sin

theorem intervalIntegrable_neg_log_sin :
    IntervalIntegrable (fun θ : ℝ => -Real.log (Real.sin θ))
      MeasureTheory.volume 0 (Real.pi / 2) := by
  have hbase : IntervalIntegrable (Real.log ∘ Real.sin)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    intervalIntegrable_log_sin
  have hEq : (Real.log ∘ Real.sin) = (fun θ : ℝ => Real.log (Real.sin θ)) := rfl
  rw [hEq] at hbase
  have hneg := hbase.neg
  exact hneg

theorem chap9S_one_eq_pi_half_mul_log_two :
    (∑' k : ℕ, chap9S 1 k) = Real.pi / 2 * Real.log 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt chap9f (-Real.log (Real.sin x)) x := by
    intro x hx
    have h0 : 0 < x := (Set.mem_Ioo.mp hx).1
    have h1 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
    exact hasDerivAt_chap9f h0 h1
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
      = chap9f (Real.pi / 2) - chap9f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      continuousOn_chap9f hderiv intervalIntegrable_neg_log_sin
  have hintegral : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
      = Real.pi / 2 * Real.log 2 := by
    have hbase := integral_log_sin_zero_pi_div_two
    have hEq : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
        = -(∫ x in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin x)) :=
      intervalIntegral.integral_neg
    rw [hEq, hbase]
    ring
  have hf0 : chap9f 0 = 0 := by
    unfold chap9f chap9E
    rw [Real.sin_zero, chap9S_zero_aux]
    simp
  have hfpi : chap9f (Real.pi / 2) = ∑' k : ℕ, chap9S 1 k := by
    unfold chap9f chap9E
    rw [Real.sin_pi_div_two, Real.log_one, mul_zero, sub_zero]
  rw [hintegral, hfpi, hf0, sub_zero] at hFTC
  exact hFTC.symm

theorem chap9D_zero : chap9D 0 = 0 := by
  have hS1 := chap9S_one_eq_pi_half_mul_log_two
  unfold chap9D
  rw [log_two_cos_zero_aux, Real.cos_zero, Real.sin_zero, Real.tan_zero,
    chap9S_zero_aux, chap9T_zero_aux, hS1]
  ring

theorem chap9D_eq_zero {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    chap9D x = 0 := by
  by_cases hx0' : x = 0
  · rw [hx0']
    exact chap9D_zero
  · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
    have hpi : 0 < Real.pi := Real.pi_pos
    have hcont : ContinuousOn chap9D (Set.Icc 0 x) :=
      continuousOn_chap9D.mono (Set.Icc_subset_Icc le_rfl hx)
    have hderiv : ∀ c ∈ Set.Ioo 0 x, HasDerivAt chap9D 0 c := by
      intro c hc
      have hc0 : 0 < c := (Set.mem_Ioo.mp hc).1
      have hcx : c < x := (Set.mem_Ioo.mp hc).2
      exact hasDerivAt_chap9D hc0 (lt_of_lt_of_le hcx hx)
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (f := chap9D)
      (f' := fun _ => (0 : ℝ)) hpos hcont hderiv
    have hne : x - 0 ≠ 0 := sub_ne_zero.mpr hx0'
    have hdiv : (chap9D x - chap9D 0) / (x - 0) = 0 := hc.symm
    have hor := (div_eq_zero_iff.mp hdiv)
    cases hor with
    | inl hnum =>
      have h0 := chap9D_zero
      linarith [hnum, h0]
    | inr hden =>
      exact absurd hden hne

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry19_catalangf`.
-/
theorem ramanujan_part1_ch9_entry19_catalangf (x : ℝ)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < 2 * Real.cos x ∧
      Summable (chapter9Entry19CentralTerm x) ∧
      Summable (chapter9Entry19TanTerm x) ∧
      (∑' k : ℕ, chapter9Entry19CentralTerm x k) =
        Real.pi / 2 * Real.log (2 * Real.cos x) +
          ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  refine ⟨?_, summable_central_aux hx0 hx, summable_tan_aux hx0 hx, ?_⟩
  · have h := cos_pos_aux hx0 hx
    linarith
  · have hEq := chap9D_eq_central hx0 hx
    have hD := chap9D_eq_zero hx0 hx
    rw [hD] at hEq
    exact sub_eq_zero.mp hEq.symm

end
end Entry19Catalangf
end Ramanujan.Part1Ch9
end

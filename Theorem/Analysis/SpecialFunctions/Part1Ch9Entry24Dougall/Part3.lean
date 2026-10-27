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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part3
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

theorem isOpen_openLens : IsOpen openLens :=
  Metric.isOpen_ball.inter Metric.isOpen_ball

theorem convex_openLens : Convex ℝ openLens :=
  (convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)

theorem isPreconnected_openLens : IsPreconnected openLens :=
  convex_openLens.isPreconnected

theorem norm_lt_one_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    ‖z‖ < 1 := by
  have h0 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
  have hdist : dist z (0 : ℂ) < 1 := Metric.mem_ball.mp h0
  rwa [dist_eq_norm, sub_zero] at hdist

theorem norm_one_sub_lt_one_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    ‖(1 : ℂ) - z‖ < 1 := by
  have h1 : z ∈ Metric.ball (1 : ℂ) 1 := hz.2
  have hdist : dist z (1 : ℂ) < 1 := Metric.mem_ball.mp h1
  rw [dist_eq_norm] at hdist
  have hrev : ‖(1 : ℂ) - z‖ = ‖z - 1‖ := norm_sub_rev _ _
  rwa [hrev]

theorem re_pos_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    0 < z.re := by
  have h1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hle : |(1 - z).re| ≤ ‖(1 : ℂ) - z‖ := Complex.abs_re_le_norm _
  have hlt : |(1 - z).re| < 1 := lt_of_le_of_lt hle h1
  have hre : (1 - z).re = 1 - z.re := by simp
  rw [hre] at hlt
  have hmem := abs_lt.mp hlt
  linarith

theorem re_one_sub_pos_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    0 < (1 - z).re := by
  have h0 := norm_lt_one_of_mem_openLens hz
  have hle : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm _
  have hlt : |z.re| < 1 := lt_of_le_of_lt hle h0
  have hmem := abs_lt.mp hlt
  have hre : (1 - z).re = 1 - z.re := by simp
  rw [hre]
  linarith

theorem mem_slitPlane_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_pos_of_mem_openLens hz)

theorem one_sub_mem_slitPlane_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    (1 : ℂ) - z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (re_one_sub_pos_of_mem_openLens hz)

theorem ne_zero_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    z ≠ 0 :=
  Complex.slitPlane_ne_zero (mem_slitPlane_of_mem_openLens hz)

theorem one_sub_ne_zero_of_mem_openLens {z : ℂ} (hz : z ∈ openLens) :
    (1 : ℂ) - z ≠ 0 :=
  Complex.slitPlane_ne_zero (one_sub_mem_slitPlane_of_mem_openLens hz)

theorem hasDerivAt_one_sub (z : ℂ) :
    HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1) z := by
  have h := (hasDerivAt_id' z).const_sub (1 : ℂ)
  simpa using h

theorem deriv_spenceFun_eq_zero {z : ℂ} (hz : z ∈ openLens) :
    deriv spenceFun z = 0 := by
  have hz0 : ‖z‖ < 1 := norm_lt_one_of_mem_openLens hz
  have hz1 : ‖(1 : ℂ) - z‖ < 1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hL1 : HasDerivAt cLi2 (cLi2Deriv z) z := hasDerivAt_cLi2 hz0
  have hL1' : HasDerivAt cLi2 (cLi2Deriv (1 - z)) (1 - z) :=
    hasDerivAt_cLi2 hz1
  have hsub := hasDerivAt_one_sub z
  have hL2 : HasDerivAt (cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w))
      (cLi2Deriv (1 - z) * (-1)) z :=
    hL1'.comp z hsub
  have hlog1 : HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log (mem_slitPlane_of_mem_openLens hz)
  have hlog_outer : HasDerivAt Complex.log ((1 - z)⁻¹) (1 - z) :=
    Complex.hasDerivAt_log (one_sub_mem_slitPlane_of_mem_openLens hz)
  have hlog2 : HasDerivAt (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))
      (((1 - z)⁻¹) * (-1)) z :=
    hlog_outer.comp z hsub
  have hprod : HasDerivAt (Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      (z⁻¹ * Complex.log (1 - z) + Complex.log z * (((1 - z)⁻¹) * (-1))) z :=
    hlog1.mul hlog2
  have hsum : HasDerivAt (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
      + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      ((cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))) z :=
    (hL1.add hL2).add hprod
  have hfun : spenceFun
      = (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) := by
    funext w
    unfold spenceFun
    simp [Function.comp, Pi.add_apply, Pi.mul_apply]
  rw [hfun]
  have hderiv := hsum.deriv
  rw [hderiv]
  have hC1 : z * cLi2Deriv z = -Complex.log (1 - z) := mul_cLi2Deriv hz0
  have hC2 : (1 - z) * cLi2Deriv (1 - z) = -Complex.log (1 - (1 - z)) :=
    mul_cLi2Deriv hz1
  have hsub2 : (1 : ℂ) - (1 - z) = z := by ring
  rw [hsub2] at hC2
  have hzne : z ≠ 0 := ne_zero_of_mem_openLens hz
  have h1ne : (1 : ℂ) - z ≠ 0 := one_sub_ne_zero_of_mem_openLens hz
  have e1 : z⁻¹ * Complex.log (1 - z) = -cLi2Deriv z := by
    have h := congrArg (fun w : ℂ => z⁻¹ * w) hC1
    simp only [← mul_assoc, inv_mul_cancel₀ hzne, one_mul, mul_neg] at h
    have h2 : cLi2Deriv z = -(z⁻¹ * Complex.log (1 - z)) := h
    calc z⁻¹ * Complex.log (1 - z)
        = -(-(z⁻¹ * Complex.log (1 - z))) := (neg_neg _).symm
      _ = -cLi2Deriv z := by rw [← h2]
  have e2 : Complex.log z * (((1 - z)⁻¹) * (-1)) = cLi2Deriv (1 - z) := by
    have h := congrArg (fun w : ℂ => (1 - z)⁻¹ * w) hC2
    simp only [← mul_assoc, inv_mul_cancel₀ h1ne, one_mul, mul_neg] at h
    have hlogeq : (1 - z)⁻¹ * Complex.log z = -cLi2Deriv (1 - z) := by
      have h2 : cLi2Deriv (1 - z) = -((1 - z)⁻¹ * Complex.log z) := h
      calc (1 - z)⁻¹ * Complex.log z
          = -(-((1 - z)⁻¹ * Complex.log z)) := (neg_neg _).symm
        _ = -cLi2Deriv (1 - z) := by rw [← h2]
    calc Complex.log z * (((1 - z)⁻¹) * (-1))
        = -((1 - z)⁻¹ * Complex.log z) := by ring
      _ = -(-cLi2Deriv (1 - z)) := by rw [hlogeq]
      _ = cLi2Deriv (1 - z) := neg_neg _
  calc (cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))
      = (cLi2Deriv z + (-cLi2Deriv (1 - z))) + ((-cLi2Deriv z) + cLi2Deriv (1 - z)) := by
        rw [e1, e2]
        ring
    _ = 0 := by ring

theorem differentiableOn_spenceFun :
    DifferentiableOn ℂ spenceFun openLens := by
  intro z hz
  have hz0 : ‖z‖ < 1 := norm_lt_one_of_mem_openLens hz
  have hz1 : ‖(1 : ℂ) - z‖ < 1 := norm_one_sub_lt_one_of_mem_openLens hz
  have hL1 : HasDerivAt cLi2 (cLi2Deriv z) z := hasDerivAt_cLi2 hz0
  have hL1' : HasDerivAt cLi2 (cLi2Deriv (1 - z)) (1 - z) :=
    hasDerivAt_cLi2 hz1
  have hsub := hasDerivAt_one_sub z
  have hL2 : HasDerivAt (cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w))
      (cLi2Deriv (1 - z) * (-1)) z :=
    hL1'.comp z hsub
  have hlog1 : HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log (mem_slitPlane_of_mem_openLens hz)
  have hlog_outer : HasDerivAt Complex.log ((1 - z)⁻¹) (1 - z) :=
    Complex.hasDerivAt_log (one_sub_mem_slitPlane_of_mem_openLens hz)
  have hlog2 : HasDerivAt (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))
      (((1 - z)⁻¹) * (-1)) z :=
    hlog_outer.comp z hsub
  have hprod : HasDerivAt (Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      (z⁻¹ * Complex.log (1 - z) + Complex.log z * (((1 - z)⁻¹) * (-1))) z :=
    hlog1.mul hlog2
  have hsum : HasDerivAt (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
      + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w)))
      ((cLi2Deriv z + cLi2Deriv (1 - z) * (-1))
        + (z⁻¹ * Complex.log (1 - z)
          + Complex.log z * (((1 - z)⁻¹) * (-1)))) z :=
    (hL1.add hL2).add hprod
  have hfun : spenceFun
      = (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) := by
    funext w
    unfold spenceFun
    simp [Function.comp, Pi.add_apply, Pi.mul_apply]
  have hdiff : DifferentiableAt ℂ
      (cLi2 + cLi2 ∘ (fun w : ℂ => (1 : ℂ) - w)
        + Complex.log * (Complex.log ∘ (fun w : ℂ => (1 : ℂ) - w))) z :=
    hsum.differentiableAt
  have hdiff2 : DifferentiableAt ℂ spenceFun z := hfun.symm ▸ hdiff
  exact hdiff2.differentiableWithinAt

theorem spenceFun_const_on_openLens :
    ∃ C : ℂ, ∀ z ∈ openLens, spenceFun z = C :=
  isOpen_openLens.exists_is_const_of_deriv_eq_zero isPreconnected_openLens
    differentiableOn_spenceFun (fun _ hz => deriv_spenceFun_eq_zero hz)

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end

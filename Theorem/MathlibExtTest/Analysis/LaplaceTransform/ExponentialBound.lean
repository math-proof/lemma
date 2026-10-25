/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/LaplaceTransform/ExponentialBound.lean -/

import Mathlib.NumberTheory.Chebyshev
import Lemma.Real.LaplaceTransform.BasicProperties
import Lemma.Real.LaplaceTransform.ExponentialBound
open MeasureTheory Asymptotics

/-!
# Tests for the Laplace exponential-bound package.
-/


example (f : ℝ → ℂ) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s :=
  laplaceConvergent_of_norm_le_exp f a C hf hC hbound hs

example (f : ℝ → ℂ) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)))
    (hC : 0 ≤ C)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (a * t)) :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} :=
  differentiableOn_laplace_of_norm_le_exp f a C hf hC hbound

example (f : ℝ → ℂ) (a : ℝ)
    (hloc : LocallyIntegrableOn f (Set.Ici 0))
    (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t)))
    {s : ℂ} (hs : a < s.re) :
    LaplaceConvergent f s :=
  laplaceConvergent_of_isBigO_exp f a hloc ho hs

example (f : ℝ → ℂ) (a : ℝ)
    (hloc : LocallyIntegrableOn f (Set.Ici 0))
    (ho : f =O[Filter.atTop] (fun t : ℝ => Real.exp (a * t))) :
    DifferentiableOn ℂ (laplace f) {s | a < s.re} :=
  differentiableOn_laplace_of_isBigO_exp f a hloc ho

example : DifferentiableOn ℂ (laplace (fun _ : ℝ => (1 : ℂ)))
    {s | 0 < s.re} := by
  exact differentiableOn_laplace_of_norm_le_exp _ 0 1
    continuous_const.aestronglyMeasurable zero_le_one (by intro t _; simp)

example {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ => (1 : ℂ)) s s⁻¹ ∧
      DifferentiableOn ℂ (laplace (fun _ : ℝ => (1 : ℂ)))
        {s | 0 < s.re} := by
  have hloc : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici 0) :=
    locallyIntegrableOn_const 1
  have hO : (fun _ : ℝ => (1 : ℂ)) =O[Filter.atTop]
      (fun t : ℝ => Real.exp (0 * t)) := by
    rw [Asymptotics.isBigO_iff]
    exact ⟨1, Filter.Eventually.of_forall fun t => by simp⟩
  exact ⟨hasLaplace_one hs,
    differentiableOn_laplace_of_isBigO_exp _ 0 hloc hO⟩

example : DifferentiableOn ℂ
    (laplace (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ)))
    {s | 1 < s.re} := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (Chebyshev.theta (Real.exp t) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    have hcomp : Measurable (fun t : ℝ => Chebyshev.theta (Real.exp t)) :=
      Chebyshev.theta_mono.measurable.comp Real.continuous_exp.measurable
    exact (Complex.continuous_ofReal.measurable.comp
      hcomp).aestronglyMeasurable
  have hC : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hbound : ∀ t : ℝ, 0 ≤ t →
      ‖(Chebyshev.theta (Real.exp t) : ℂ)‖ ≤ Real.log 4 * Real.exp (1 * t) := by
    intro t ht
    have hpos : 0 ≤ Real.exp t := le_of_lt (Real.exp_pos t)
    have hle := @Chebyshev.theta_le_log4_mul_x (Real.exp t) hpos
    have hnn := @Chebyshev.theta_nonneg (Real.exp t)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc Chebyshev.theta (Real.exp t) ≤ Real.log 4 * Real.exp t := hle
      _ = Real.log 4 * Real.exp (1 * t) := by rw [one_mul]
  exact differentiableOn_laplace_of_norm_le_exp _ 1 _ hmeas hC hbound


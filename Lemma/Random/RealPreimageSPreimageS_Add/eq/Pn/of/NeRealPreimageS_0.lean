import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


private lemma real_inter [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] [DecidableEq S] (M : Model Θ S A) (θ : Θ) (t t' : ℕ) (x y : S) :
    (M θ).real (s t ⁻¹' {x} ∩ s t' ⁻¹' {y}) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s t' ω = y then (1:ℝ) else 0) ∂(M θ) := by
  rw [← integral_indicator_one ((s_meas t (measurableSet_singleton x)).inter
    (s_meas t' (measurableSet_singleton y)))]
  congr 1
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : s t' ω = y <;> simp [Set.indicator, h1, h2]

/--
On a reachable state (`Pr(s[t] = x) ≠ 0`), `Pr(s[t+n] = y | s[t] = x) = Pn θ n x y` (time-homogeneous `n`-step transition).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t n : ℕ)
  (x y : S)
  (h₀ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (s (t + n) ⁻¹' {y}) = M.Pn θ n x y := by
-- proof
  rw [measureReal_def, cond_apply (s_meas t (measurableSet_singleton x)), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, real_inter,
    show (∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + n) ω = y then (1:ℝ) else 0) ∂(M θ)) =
      (M θ).real (s t ⁻¹' {x}) * M.Pn θ n x y from Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable (M := M) θ (ind_fst_sm y) (Real.Norm_Eq12.le.One y) t n x,
    inv_mul_cancel_left₀ h₀]


-- created on 2026-10-06

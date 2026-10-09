import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Measurable_S
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


private lemma real_inter [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] [DecidableEq S] {r : ℕ → (ℕ → ℝ × S × A) → ℝ} {s : ℕ → (ℕ → ℝ × S × A) → S} {a : ℕ → (ℕ → ℝ × S × A) → A} (h₁ : ∀ t, (· t) = (r t, s t, a t)) (M : Model Θ S A) (θ : Θ) (t t' : ℕ) (x y : S) :
    (M θ).real (s t ⁻¹' {x} ∩ s t' ⁻¹' {y}) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s t' ω = y then (1:ℝ) else 0) ∂(M θ) := by
  rw [← integral_indicator_one ((Random.Measurable_S h₁ t (measurableSet_singleton x)).inter
    (Random.Measurable_S h₁ t' (measurableSet_singleton y)))]
  congr 1
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : s t' ω = y <;> simp [Set.indicator, h1, h2]

/--
On a reachable state (`Pr(s[t] = x) ≠ 0`), `Pr(s[t+n] = y | s[t] = x) = Pn θ n x y` (time-homogeneous `n`-step transition).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t n : ℕ)
  (x y : S)
  (h₂ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ((M θ)[|s t ⁻¹' {x}]).real (s (t + n) ⁻¹' {y}) = M.Pn θ n x y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  rw [measureReal_def, cond_apply (Random.Measurable_S h₁ t (measurableSet_singleton x)), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ← measureReal_def, ← measureReal_def, real_inter h₁,
    show (∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + n) ω = y then (1:ℝ) else 0) ∂(M θ)) =
      (M θ).real (s t ⁻¹' {x}) * M.Pn θ n x y from Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable h₁ (M := M) θ (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) t n x,
    inv_mul_cancel_left₀ h₂]


-- created on 2026-10-06

import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Real.Sum_Eq.eq.One
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Measurable_S
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
State marginal of the trajectory model: `Pr(s[t] = y) = ∑ x, init {x} * Pn θ t x y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ)
  (y : S) :
-- imply
  (M θ).real (state t ⁻¹' {y}) = ∑ x, M.env.init.real {x} * M.Pn θ t x y := by
-- proof
  rw [← integral_indicator_one (Random.Measurable_S t (measurableSet_singleton y))]
  have h₁ : ∀ ω, (state t ⁻¹' {y}).indicator (1 : (ℕ → ℝ × S × A) → ℝ) ω =
      ∑ x, (if state 0 ω = x then (1:ℝ) else 0) * (if (ω (0 + t)).2.1 = y then (1:ℝ) else 0) := by
    intro ω
    rw [← Finset.sum_mul, Sum_Eq.eq.One, one_mul, zero_add]
    by_cases h : state t ω = y <;> simp [Set.indicator, h] <;> exact h
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => by
    exact Integrable.of.Measurable (M := M) (fun ω => (state 0 ω, state (0 + t) ω)) ((Random.Measurable_S 0).prodMk (Random.Measurable_S (0 + t)))
      θ (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable (M := M) θ (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) 0 t x, RealPreimageS0.eq.Real]
  rfl


-- created on 2026-10-06

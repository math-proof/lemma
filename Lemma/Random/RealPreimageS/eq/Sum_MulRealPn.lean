import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Real.Sum_Eq.eq.One
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


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
  (M θ).real (s t ⁻¹' {y}) = ∑ x, M.env.init.real {x} * M.Pn θ t x y := by
-- proof
  rw [← integral_indicator_one (s_meas t (measurableSet_singleton y))]
  have h₁ : ∀ ω, (s t ⁻¹' {y}).indicator (1 : (ℕ → ℝ × S × A) → ℝ) ω =
      ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * (if (ω (0 + t)).2.1 = y then (1:ℝ) else 0) := by
    intro ω
    rw [← Finset.sum_mul, Real.Sum_Eq.eq.One, one_mul, zero_add]
    by_cases h : s t ω = y <;> simp [Set.indicator, h] <;> exact h
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => by
    exact integrable_ind_h M θ (fun ω => (s 0 ω, s (0 + t) ω))
      ((s_meas 0).prodMk (s_meas (0 + t))) (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable (M := M) θ (ind_fst_sm y) (Real.Norm_Eq12.le.One y) 0 t x, Random.RealPreimageS0.eq.Real]
  rfl


-- created on 2026-10-06

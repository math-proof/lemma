import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Pn.eq.Integral
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Real.Sum_Eq.eq.One
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
State marginal of the trajectory model: `Pr(s[t] = y) = ∑ x, init {x} * Pn θ t x y`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (y : S) :
-- imply
  (M θ).real (s t ⁻¹' {y}) = ∑ x, M.env.init.real {x} * M.Pn θ t x y := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  rw [← integral_indicator_one (Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton y))]
  have h₁ : ∀ ω, (s t ⁻¹' {y}).indicator (1 : (ℕ → ℝ × S × A) → ℝ) ω =
      ∑ x, (if s 0 ω = x then (1:ℝ) else 0) * (if (ω (0 + t)).2.1 = y then (1:ℝ) else 0) := by
    intro ω
    rw [← Finset.sum_mul, Sum_Eq.eq.One, one_mul, zero_add]
    by_cases h : s t ω = y <;> simp [Set.indicator, h] <;> exact h
  simp_rw [h₁]
  rw [integral_finsetSum _ (fun x _ => by
    exact Integrable.of.Measurable (M := M) (fun ω => (s 0 ω, s (0 + t) ω)) ((Random.Measurable.of.All_Eq.snd.fst h₀ 0).prodMk (Random.Measurable.of.All_Eq.snd.fst h₀ (0 + t)))
      θ (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Integral_MulEqS.eq.MulRealW.of.All_LeNorm.StronglyMeasurable h₀ (M := M) (Real.StronglyMeasurable_Eq12 y)
    (Norm_Eq12.le.One y) θ 0 t x, RealPreimageS0.eq.Real h₀, ← Pn.eq.Integral (M := M) θ t x y]


-- created on 2026-10-06

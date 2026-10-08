import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Map.eq.StageK
import Lemma.Random.Measurable_S
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.StronglyMeasurable.discrete
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x} * g(ω[t])] = Pr(s[t] = x) * ∫ z, g z ∂(stageK θ x)` for a bounded strongly measurable `g`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {g : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (t : ℕ)
  (x : S) :
-- imply
  ∫ ω, (if state t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
    (M θ).real (state t ⁻¹' {x}) * ∫ z, g z ∂(M.stageK θ x) := by
-- proof
  have hm : StronglyMeasurable (fun z : ℝ × S × A => (if z.2.1 = x then (1:ℝ) else 0) * g z) :=
    ((StronglyMeasurable.discrete (fun y : S => if y = x then (1:ℝ) else 0)).comp_measurable measurable_snd.fst).mul hg
  have : IsProbabilityMeasure ((M θ).map (state t)) :=
    Measure.isProbabilityMeasure_map (Random.Measurable_S t).aemeasurable
  have e1 : ∫ ω, (if state t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
      ∫ z, (if z.2.1 = x then (1:ℝ) else 0) * g z ∂((M θ).map (fun ω => ω t)) := by
    rw [integral_map (measurable_pi_apply t).aemeasurable hm.aestronglyMeasurable]; rfl
  rw [e1, Map.eq.StageK, Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable hm (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A => z.2.1 = x)) hC)]
  simp_rw [Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hg hC θ x]
  have h₂ : ∀ y', (if y' = x then (1:ℝ) else 0) * ∫ z, g z ∂(M.stageK θ y') =
      (if y' = x then 1 else 0) * ∫ z, g z ∂(M.stageK θ x) := by
    intro y'; by_cases h : y' = x <;> simp [h]
  simp_rw [h₂]
  rw [integral_mul_const]
  congr 1
  have h₃ : (fun y' : S => if y' = x then (1:ℝ) else 0) = ({x} : Set S).indicator 1 := by
    funext y'; simp [Set.indicator_apply]
  rw [h₃, integral_indicator_one (measurableSet_singleton x), measureReal_def, measureReal_def,
    Measure.map_apply (Random.Measurable_S t) (measurableSet_singleton x)]


-- created on 2026-10-07

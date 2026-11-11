import Lemma.Random.Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulIte.eq.MulKroneckerDeltaIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Def.Analysis.SpecialFunctions.TensorFunctions
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Nat Random Real


/--
`𝔼[1{s[t] = x} * g(ω[t])] = ℙ(s[t] = x) * ∫ z, g z ∂(stageK θ x)` for a bounded strongly measurable `g`
on the continuous-action trajectory model (`DensityModel`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
  {g : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * ∫ z, g z ∂(M.stageK θ x) := by
-- proof
  have hst : ∀ ω, s t ω = (ω t).2.1 := fun ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have hm : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => (if z.2.1 = x then (1:ℝ) else 0) * g z) :=
    ((StronglyMeasurable.of_discrete (f := (fun y : 𝒮 => if y = x then (1:ℝ) else 0))).comp_measurable measurable_snd.fst).mul hg
  have : IsProbabilityMeasure ((M θ).map (s t)) :=
    inferInstance
  have e1 : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M θ) =
      ∫ z, (if z.2.1 = x then (1:ℝ) else 0) * g z ∂((M θ).map (fun ω => ω t)) := by
    rw [integral_map (measurable_pi_apply t).aemeasurable hm.aestronglyMeasurable]; simp only [hst]
  rw [e1, Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity h₀,
    Integral.eq.Integral.of.All_LeNorm.StronglyMeasurable hm
      (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × 𝒮 × 𝒜 => z.2.1 = x)) hC)]
  simp_rw [Integral_MulIte.eq.MulKroneckerDeltaIntegral.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hg hC θ x]
  have h₂ : ∀ y', (KroneckerDelta y' x : ℝ) * ∫ z, g z ∂(M.stageK θ y') =
      (KroneckerDelta y' x : ℝ) * ∫ z, g z ∂(M.stageK θ x) := by
    intro y'; by_cases h : y' = x <;> simp [h, KroneckerDelta]
  simp_rw [h₂]
  rw [integral_mul_const]
  congr 1
  have h₃ : (fun y' : 𝒮 => (KroneckerDelta y' x : ℝ)) = ({x} : Set 𝒮).indicator 1 := by
    funext y'; by_cases h : y' = x <;> simp [h, KroneckerDelta]
  rw [h₃, integral_indicator_one (measurableSet_singleton x), measureReal_def, measureReal_def,
    Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h₀ t) (measurableSet_singleton x)]


-- created on 2026-11-04

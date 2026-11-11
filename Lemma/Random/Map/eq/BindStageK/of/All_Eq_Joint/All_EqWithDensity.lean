import Lemma.Random.EqMapStageK_12.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindK.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random


/--
The stage `ω[t]` is distributed as `stageK θ ∘ₘ law(s[t])` (continuous-action model).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => ω t) = M.stageK θ ∘ₘ (M θ).map (s t) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  have h : (M θ).map (s t) = ((M θ).map (fun ω => ω t)).map (fun z => z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply t)]; rfl
  rw [h]
  cases t with
  | zero =>
    rw [Map.eq.BindStageK.of.All_EqWithDensity, EqMapStageK_12.of.All_EqWithDensity]
  | succ t =>
    rw [Map.eq.BindK.of.All_EqWithDensity, DensityModel.K, ← Measure.comp_assoc,
      EqMapStageK_12.of.All_EqWithDensity]


-- created on 2026-10-20

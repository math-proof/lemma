import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


private lemma delta_meas
  [MeasurableSpace 𝒮] [MeasurableSpace 𝒜]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {V : 𝒮 → ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hV : Measurable V)
  (γ : ℝ)
  (j : ℕ) :
-- imply
  Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => r j ω + γ * V (s (j + 1) ω) - V (s j ω)) :=
-- proof
  ((Random.Measurable.of.All_Eq.fst h₀ j).add
      ((hV.comp (Random.Measurable.of.All_Eq.snd.fst h₀ (j + 1))).const_mul γ)).sub
    (hV.comp (Random.Measurable.of.All_Eq.snd.fst h₀ j))

/--
`δ[j] • ψ(s[t], a[t])` is integrable under the trajectory model.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {ψ : 𝒮 → 𝒜 → E}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 ↦ M.policy.prob θ z.1 z.2))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hMs : ∃ Ms : ℝ, ∀ y u, ‖ψ y u‖ ≤ Ms)
  (θ : Θ)
  (t j : ℕ) :
-- imply
  Integrable (fun ω => (r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω)) •
    ψ (s t ω) (a t ω)) (M θ) := by
-- proof
  obtain ⟨Ms, hMs⟩ := hMs
  have hV : Measurable (M.V0 θ γ) := Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ
  have hX : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω)) :=
    (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  refine Integrable.of_bound (C := (3 / (1 - γ) - 1) * |M.env.R| * Ms)
    ((delta_meas h₁ hV γ j).stronglyMeasurable.smul
      (hψ.comp_measurable hX)).aestronglyMeasurable ?_
  filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico (M := M) h₀ h₁ θ] with ω h
  rw [norm_smul]
  exact mul_le_mul (h j) (hMs (s t ω) (a t ω)) (norm_nonneg _)
    ((norm_nonneg _).trans (h j))


-- created on 2026-10-06
-- updated on 2026-11-13

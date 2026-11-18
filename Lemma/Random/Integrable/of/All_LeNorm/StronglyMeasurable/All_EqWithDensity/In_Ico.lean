import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Instance.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`G[t] • ψ(s[t], a[t])` is integrable under the continuous-action trajectory model
when `ψ` is bounded and strongly measurable.
Continuous-action counterpart of `Random.Integrable.of.In_Ico`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {C : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {ψ : 𝒮 → 𝒜 → ℰ}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable fun p : 𝒮 × 𝒜 => ψ p.1 p.2)
  (hC : ∀ y u, ‖ψ y u‖ ≤ C)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ)
  (t : ℕ) :
-- imply
  Integrable (fun ω => ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω • ψ (s t ω) (a t ω)) (M θ) := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  have hX : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω)) :=
    (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  have hpR : Measurable (fun ω k ↦ r k ω) :=
    Measurable.of_eval fun k => measurable_fst.comp (measurable_pi_apply k)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hG : Measurable G := hfG.comp hpR
  have hψω : StronglyMeasurable fun ω => ψ (s t ω) (a t ω) :=
    hψ.comp_measurable hX
  have hbound : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ (1 - γ)⁻¹ * |R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) hR θ] with ω h
    have hb : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k)
    have hGω : G ω = ∑' k, γ ^ k * r (t + k) ω := by
      unfold G Dot.dot Function.getSliceFrom
      rfl
    rw [hGω]
    exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) hb
  refine Integrable.of_bound (C := (1 - γ)⁻¹ * |R| * C)
    (hG.aestronglyMeasurable.smul hψω.aestronglyMeasurable) ?_
  filter_upwards [hbound] with ω hGω
  rw [norm_smul]
  exact mul_le_mul hGω (hC (s t ω) (a t ω)) (norm_nonneg _) ((norm_nonneg _).trans hGω)


-- created on 2026-11-14
-- updated on 2026-11-18

import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Kernel


/--
`𝔼[φ(s[t], a[t])] = ∫ y, (∫ u, π_θ(u | y) • φ y u du) ∂law(s[t])` under the continuous-action
trajectory model, for an integrable integrand.
Continuous-action counterpart of `Random.Integral.eq.Sum_Sum_SMul`: Finset sums become
integrals against `law(s[t])` and the reference measure of `𝒜`, via `Model.stageK`.
-/
@[path]
private lemma main
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {φ : 𝒮 → 𝒜 → ℰ}
  {C : ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hφ : StronglyMeasurable (Function.uncurry φ))
  (hC : ∀ y u, ‖φ y u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, φ (s t ω) (a t ω) ∂(M.traj θ) =
    ∫ y, (∫ u, M.π[θ] y u • φ y u ∂μ.measure) ∂((M.traj θ).map (s t)) := by
-- proof
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₀ t
  have hsa : Measurable (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => (s t ω, a t ω)) := hs.prodMk ha
  have hf : StronglyMeasurable (fun z : ℝ × 𝒮 × 𝒜 => φ z.2.1 z.2.2) :=
    hφ.comp_measurable (measurable_snd.fst.prodMk measurable_snd.snd)
  have hCb : ∀ z : ℝ × 𝒮 × 𝒜, ‖φ z.2.1 z.2.2‖ ≤ C := fun z => hC _ _
  have e := integral_map (μ := M.traj θ) hsa.aemeasurable
    (f := fun p : 𝒮 × 𝒜 => φ p.1 p.2) hφ.aestronglyMeasurable
  refine e.symm.trans ?_
  have hmap : (M.traj θ).map (fun ω => (s t ω, a t ω)) =
      ((M.traj θ).map (fun ω => ω t)).map (fun z => (z.2.1, z.2.2)) := by
    have hs' : s t = fun ω => (ω t).2.1 := funext fun ω =>
      (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha' : a t = fun ω => (ω t).2.2 := funext fun ω =>
      (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    rw [hs', ha', Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  rw [hmap, Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t]
  have e_map := integral_map (μ := M.stageK θ ∘ₘ (M.traj θ).map (s t))
    (measurable_snd.fst.prodMk measurable_snd.snd).aemeasurable
    (f := fun p : 𝒮 × 𝒜 => φ p.1 p.2) hφ.aestronglyMeasurable
  refine e_map.trans ?_
  have : IsProbabilityMeasure (M.traj θ) := inferInstance
  have : IsProbabilityMeasure ((M.traj θ).map (s t)) := inferInstance
  have hInt : Integrable (fun z : ℝ × 𝒮 × 𝒜 => φ z.2.1 z.2.2)
      (M.stageK θ ∘ₘ (M.traj θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hCb)
  rw [Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  congr 1
  funext y
  have e₁ :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hCb θ y
  have e₂ : ∀ u, ∫ ρ, φ (ρ, y, u).2.1 (ρ, y, u).2.2 ∂(M.reward (y, u) : Measure ℝ) = φ y u :=
    fun u => by
    simp
  simp_rw [e₁, e₂]


-- created on 2026-10-20
-- updated on 2026-11-17
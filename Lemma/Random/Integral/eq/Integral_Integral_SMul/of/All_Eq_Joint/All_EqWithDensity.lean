import Lemma.Kernel.Integral.eq.Integral_Integral.of.Integrable_Bind
import Lemma.Random.Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Kernel


/--
`𝔼[φ(s[t], a[t])] = ∫ y, (∫ u, π_θ(u | y) • φ y u du) ∂law(s[t])` under the continuous-action
trajectory model, for an integrable integrand.
Continuous-action counterpart of `Random.Integral.eq.Sum_Sum_SMul`: Finset sums become
integrals against `law(s[t])` and the reference measure of `A`, via `DensityModel.stageK`.
-/
@[path]
private lemma main
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {φ : S → A → E}
  {C : ℝ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hφ : StronglyMeasurable (Function.uncurry φ))
  (hC : ∀ y u, ‖φ y u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, φ (s t ω) (a t ω) ∂(M θ) =
    ∫ y, (∫ u, M.policy.prob θ y u • φ y u ∂ReferenceMeasure.measure) ∂((M θ).map (s t)) := by
-- proof
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₀ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₀ t
  have hsa : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := hs.prodMk ha
  have hf : StronglyMeasurable (fun z : ℝ × S × A => φ z.2.1 z.2.2) :=
    hφ.comp_measurable (measurable_snd.fst.prodMk measurable_snd.snd)
  have hCb : ∀ z : ℝ × S × A, ‖φ z.2.1 z.2.2‖ ≤ C := fun z => hC _ _
  have e := integral_map (μ := M θ) hsa.aemeasurable
    (f := fun p : S × A => φ p.1 p.2) hφ.aestronglyMeasurable
  refine e.symm.trans ?_
  have hmap : (M θ).map (fun ω => (s t ω, a t ω)) =
      ((M θ).map (fun ω => ω t)).map (fun z => (z.2.1, z.2.2)) := by
    have hs' : s t = fun ω => (ω t).2.1 := funext fun ω =>
      (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha' : a t = fun ω => (ω t).2.2 := funext fun ω =>
      (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    rw [hs', ha', Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  rw [hmap, Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ t]
  have e_map := integral_map (μ := M.stageK θ ∘ₘ (M θ).map (s t))
    (measurable_snd.fst.prodMk measurable_snd.snd).aemeasurable
    (f := fun p : S × A => φ p.1 p.2) hφ.aestronglyMeasurable
  refine e_map.trans ?_
  have := M.env.init_prob
  have : IsProbabilityMeasure (M θ) := inferInstance
  have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
  have hInt : Integrable (fun z : ℝ × S × A => φ z.2.1 z.2.2)
      (M.stageK θ ∘ₘ (M θ).map (s t)) :=
    Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hCb)
  rw [Integral.eq.Integral_Integral.of.Integrable_Bind hInt]
  congr 1
  funext y
  have e₁ : ∫ z, φ z.2.1 z.2.2 ∂(M.stageK θ y) =
      ∫ u, M.policy.prob θ y u • ∫ ρ, φ y u ∂(M.env.reward (y, u))
        ∂ReferenceMeasure.measure :=
    Integral.eq.Integral_SMul.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hCb θ y
  have e₂ : ∀ u, ∫ ρ, φ y u ∂(M.env.reward (y, u)) = φ y u := fun u => by
    have := M.env.reward_markov
    simp
  simp_rw [e₁, e₂]


-- created on 2026-10-20

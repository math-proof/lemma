import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/--
Generalized advantage estimation for a finite action alphabet and a general state
(Schulman et al., arXiv 1506.02438). The action reference measure is counting measure,
so `π_θ(· | s)` is a probability mass function: a language-model policy, with a
continuous context as the state and the vocabulary as the action. `∑ u, g s u` is the
action-integral bound of the continuous-action GAE, and `V_θ[t] δ k := M.V θ γ (t + k) (δ k)`.
- [GAE (discrete)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico)
- [GAE (continuous)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮] [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ ℓ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (hfactor : DensityModel.IsConditionalProbability M r s a)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₄ : sup[x] (∑ u, g x u) < ∞)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)))
  (hMs : sup[y, u] ‖∇[θ] Real.log (M.policy.prob θ y u)‖ < ∞) :
-- imply
  letI : DensityModel.IsPolicyTrajectory M r s a := hfactor.htr
  letI : DensityModel.AbsContJointAS M a s := hfactor.haj
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      ((((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  obtain ⟨Cg, hCg⟩ := id h₄
  have h₄le : ∀ x, ∑ u, g x u ≤ Cg := fun x => hCg ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hVm : ∀ k, Measurable (M.V θ γ k) := fun _ => Measurable.of_discrete
  have h₅sup : sup[x] ∫ u, g x u ∂μ.measure < ∞ :=
    ⟨Cg, by
      rintro _ ⟨x, rfl⟩
      rw [hμ, integral_count]
      exact h₄le x⟩
  have hMspath : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
      ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞ :=
    ⟨Ms, by
      rintro _ ⟨(sb, ab), rfl⟩
      simpa [funext fun θ' =>
        congrArg Real.log (hfactor.factor θ' 0 (sb 0) (ab 0))] using
        hMsle (sb 0) (ab 0)⟩
  apply GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
    (M := M) h₀ h₁ hfactor hπ hVm
    (fun t sb ab =>
      (funext fun θ' => hfactor.factor θ' t (sb t) (ab t)) ▸ h₂ (sb t) (ab t))
    (fun θ t sb ab => by
      simpa [funext fun θ' => hfactor.factor θ' t (sb t) (ab t)] using
        h₃ θ (sb t) (ab t))
  ·
    intro x
    rw [hμ]
    apply integrable_count_iff.mpr Summable.of_finite
  ·
    exact h₅sup
  ·
    apply hφ
  ·
    exact hMspath


-- created on 2026-11-01
-- updated on 2026-11-14

import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
import Lemma.Measure.All_Integrable_Measure.GtInftySup_Integral.of.GtInftySup_Sum
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Real
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
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (hfactor : Model.IsConditionalProbability M r s a)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₂ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₃ : sup[sₜ] (∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.π[θ] z.1 z.2)))
  (hMs : sup[y, u] ‖∇[θ] Real.log (M.π[θ] y u)‖ < ∞) :
-- imply
  letI : Model.IsPolicyTrajectory M r s a := hfactor.htr
  letI : Model.AbsContJointAS M a s := hfactor.haj
  have : ∀ θ', PSpace (M.traj θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((γ * ℓ) ^ (id : ℕ → ℕ) ⬝ᵥ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M.traj θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖∇[θ] Real.log (M.π[θ] y u)‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  have hVm : ∀ k, Measurable (M.V θ γ k) := fun _ => Measurable.of_discrete
  have hfe : ∀ sₜ aₜ,
      (fun θ => M.π[θ] sₜ aₜ) =
        (fun θ => (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)) :=
    fun sₜ aₜ => funext fun θ' => hfactor.factor θ' 0 sₜ aₜ
  have hnorm : ∀ sₜ aₜ,
      (fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) =
        (fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)‖) :=
    fun sₜ aₜ => funext fun θ =>
      congrArg (fun φ : Θ → ℝ => ‖gradient φ θ‖) (hfe sₜ aₜ)
  have h₃sum : sup[sₜ] (∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)‖)) < ∞ := by
    have hf :
        (fun sₜ => ∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) =
          (fun sₜ => ∑ aₜ, sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)‖)) :=
      funext fun sₜ =>
        congrArg (fun f => ∑ aₜ, f aₜ)
          (funext fun aₜ => congrArg (fun f => sSup (Set.range f)) (hnorm sₜ aₜ))
    simpa [hf] using h₃
  have hpack :=
    All_Integrable_Measure.GtInftySup_Integral.of.GtInftySup_Sum
      (g := fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)‖)) h₃sum
  have hIntg := hpack.1
  have h₃int := hpack.2
  have hBddP : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = aₜ | s[0] = sₜ) : ℝ)‖) := by
    intro sₜ aₜ
    simpa [hnorm sₜ aₜ] using hBdd sₜ aₜ
  have hMspath : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
    ‖∇[θ] (ℙ[M.traj θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞ :=
    ⟨Ms, by
      rintro _ ⟨⟨sb, ab⟩, rfl⟩
      simpa [funext fun θ' =>
        congrArg Real.log (hfactor.factor θ' 0 (sb 0) (ab 0))] using
        hMsle (sb 0) (ab 0)⟩
  apply GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
    (M := M) h₀ h₁ hfactor hπ hVm
    (fun t sb ab =>
      (funext fun θ' => hfactor.factor θ' t (sb t) (ab t)) ▸ h₂ (sb t) (ab t))
    h₃int hBddP hIntg
  ·
    apply hφ
  ·
    exact hMspath

-- created on 2026-11-01
-- updated on 2026-11-16

import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_IntegrableMeasureAndGtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
import Lemma.Measure.All_IntegrableMeasureAndGtInftySup.of.GtInftySup
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.EqProb
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000


/--
Generalized advantage estimation for a finite action alphabet and a general state
(Schulman et al., arXiv 1506.02438). The action reference measure is counting measure,
so `π_θ(· | s)` is a probability mass function: a language-model policy, with a
continuous context as the state and the vocabulary as the action. `∑ u, g s u` is the
action-integral bound of the continuous-action GAE, and `V_θ[t] δ k := M.V0 θ γ (δ k)`.
- [GAE (discrete)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico)
- [GAE (continuous)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)

Special case of dens FunSMul Subset_Ico: discharge Integrable/integral bounds from the
Finset-sum hypothesis via All_IntegrableMeasureAndGtInftySup.of.GtInftySup,
and the score StronglyMeasurable hypothesis via StronglyMeasurable.of_discrete.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Countable S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (hfactor : DensityModel.IsConditionalProbability M r s a)
  (h₁ : ∀ t («\sf{s}» : ℕ ⇀ S) («\sf{a}» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)))
  (h₂ : ∃ (g : S → A → ℝ),
    (∀ θ t («\sf{s}» : ℕ ⇀ S) («\sf{a}» : ℕ ⇀ A),
      ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
        g «\sf{s}»[t] «\sf{a}»[t]) ∧
    (sup[x] (∑ u, g x u) < ∞))
  (hMs : sup[«\sf{s}» : ℕ ⇀ S, «\sf{a}» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    hfactor.htr.singlePSpace_as (haj := hfactor.haj) θ t
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _ δ k => M.V0 θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ (γ ^ range (k + 1)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]))) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  obtain ⟨g, ⟨h₂bound, h₂sup⟩⟩ := h₂
  have h₂dens :
      ∃ (g : S → A → ℝ),
        (∀ θ t («\sf{s}» : ℕ ⇀ S) («\sf{a}» : ℕ ⇀ A),
          ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
            g «\sf{s}»[t] «\sf{a}»[t]) ∧
        (∀ x, Integrable (g x) ReferenceMeasure.measure) ∧
        (sup[x] (∫ u, g x u ∂ReferenceMeasure.measure) < ∞) := by
    refine ⟨g, h₂bound, ?_⟩
    exact All_IntegrableMeasureAndGtInftySup.of.GtInftySup h₂sup
  have hφ : StronglyMeasurable
      (fun ((s0, a0) : S × A) => ∇[θ] (ℙ[M θ](a[0] = a0 | s[0] = s0) : ℝ).log) :=
    StronglyMeasurable.of_discrete
  exact GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_IntegrableMeasureAndGtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
    h₀ hfactor h₁ h₂dens hφ hMs


-- created on 2026-11-02
-- updated on 2026-11-03

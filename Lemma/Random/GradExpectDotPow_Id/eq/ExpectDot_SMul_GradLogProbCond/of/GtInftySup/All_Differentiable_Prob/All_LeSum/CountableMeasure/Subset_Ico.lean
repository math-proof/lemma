import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_Integrable_Measure.GtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
import Lemma.Measure.All_Integrable_Measure.GtInftySup_Integral.of.GtInftySup_Sum
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.EqProb
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000


/--
In industry LLM / RLHF training (PPO and related policy-gradient fine-tunes),
GAE is the usual advantage estimator for next-token updates. The state is the
context — a continuous or otherwise general prompt / conversation embedding —
and the action is the next token from a finite vocabulary, so the action
reference measure is counting measure and `π_θ(· | s)` is the model's
next-token probability mass function. With discount `γ` and GAE parameter `λ`
in `[0, 1)`, the gradient of the discounted return equals the expected
GAE-weighted score `∇ log π_θ(a_t | s_t)` on sampled tokens — the identity
production trainers rely on when they backprop through log-probs.
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
    exact All_Integrable_Measure.GtInftySup_Integral.of.GtInftySup_Sum h₂sup
  have hφ : StronglyMeasurable
      (fun ((s0, a0) : S × A) => ∇[θ] (ℙ[M θ](a[0] = a0 | s[0] = s0) : ℝ).log) :=
    StronglyMeasurable.of_discrete
  exact GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_Integrable_Measure.GtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
    h₀ hfactor h₁ h₂dens hφ hMs


-- created on 2026-11-02
-- updated on 2026-11-04 13:37:57

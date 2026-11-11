import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_Integrable_Measure.GtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Instance.Algebra.Module.HDiv
import Theorem.Probability.CondExpectation
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.MeasurableIntegral
import Lemma.Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000



private lemma smul_fderiv_log
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (hdiff : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (θ : Θ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  M.policy.prob θ x u • fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ =
    fderiv ℝ (fun κ => M.policy.prob κ x u) θ := by
-- proof
  if h : M.policy.prob θ x u = 0 then
    rw [h, zero_smul]
    exact (IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun κ => by
      rw [h]
      exact M.policy.nonneg κ x u)).symm
  else
    rw [fderiv.log ((hdiff x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]


/-- Integral against a density-policy kernel is the reference integral weighted by `π`. -/
private lemma integral_kernel
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : 𝒜 → E}
-- given
  (θ : Θ)
  (x : 𝒮) :
-- imply
  ∫ u, f u ∂(M[x] θ) =
    ∫ u, M.policy.prob θ x u • f u ∂(ReferenceMeasure.measure : Measure 𝒜) := by
-- proof
  have hπm : Measurable (M.policy.dens θ x) :=
    (M.policy.measurable_dens θ).comp (Measurable.prodMk measurable_const measurable_id)
  have hker : M[x] θ =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ x) := by
    change M.policy.kernel θ x =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ x)
    exact Kernel.withDensity_apply (Kernel.const 𝒮 (ReferenceMeasure.measure : Measure 𝒜))
      (M.policy.measurable_dens θ) x
  rw [hker, integral_withDensity_eq_integral_toReal_smul hπm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ x u)]


/-- Importance weight `π' • ((c • ∇π) / π')` equals the on-policy score `π • (c • ∇ log π)`. -/
private lemma is_weight_eq_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ θ' : Θ}
-- given
  (hdiff : ∀ x u, Differentiable ℝ (fun κ => M.policy.prob κ x u))
  (hvanish : ∀ x u, M.policy.prob θ' x u ≠ 0 ∨ M.policy.prob θ x u = 0)
  (x : 𝒮)
  (u : 𝒜)
  (c : ℝ) :
-- imply
  M.policy.prob θ' x u •
      ((c • ∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u) =
    M.policy.prob θ x u • (c • ∇[θ] Real.log (M.policy.prob θ x u)) := by
-- proof
  let e : StrongDual ℝ Θ ≃ₗᵢ[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm
  if hq : M.policy.prob θ' x u = 0 then
    have hp : M.policy.prob θ x u = 0 := (hvanish x u).resolve_left (not_ne_iff.mpr hq)
    simp [hq, hp, HDiv.hDiv]
  else
    have hgrad := smul_fderiv_log (M := M) hdiff θ x u
    calc
      _ = c • ∇[θ] (M.policy.prob θ x u) := by
        simp only [HDiv.hDiv, smul_smul]
        exact congrArg (fun t => t • ∇[θ] (M.policy.prob θ x u)) (by field_simp [hq])
      _ = c • e (fderiv ℝ (fun κ => M.policy.prob κ x u) θ) := by
        simp [e, gradient]
      _ = e (c • fderiv ℝ (fun κ => M.policy.prob κ x u) θ) := by
        rw [map_smul]
      _ = e (c • (M.policy.prob θ x u •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ)) := by
        rw [← hgrad]
      _ = e ((M.policy.prob θ x u * c) •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ) := by
        rw [smul_smul, mul_comm]
      _ = M.policy.prob θ x u • (c •
          e (fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ)) := by
        rw [smul_smul, map_smul]
      _ = M.policy.prob θ x u • (c • ∇[θ] Real.log (M.policy.prob θ x u)) := by
        simp [e, gradient]



/-- The proposal kernel's canonical density is `π_θ'` almost everywhere. -/
private lemma kernel_pdf
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ' : Θ}
  {x : 𝒮}
-- given
  (hμ : (M[x] θ' : Measure 𝒜) =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ' x))
  (hdens : Measurable (M.policy.dens θ' x))
  (hSP : SinglePSpace (M[x] θ') (id : 𝒜 → 𝒜)) :
-- imply
  (fun u => ((M[x] θ').prob (id : 𝒜 → 𝒜) u).toReal) =ᵐ[ReferenceMeasure.measure]
    M.policy.prob θ' x := by
-- proof
  have hmap : (M[x] θ').map (id : 𝒜 → 𝒜) =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ' x) := by
    rw [Measure.map_id, hμ]
  have hrn :
      ((M[x] θ').map (id : 𝒜 → 𝒜)).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure]
        M.policy.dens θ' x := by
    rw [hmap]
    exact Measure.rnDeriv_withDensity
      (ν := (ReferenceMeasure.measure : Measure 𝒜)) hdens
  filter_upwards [hrn] with u hu
  simp only [Measure.prob]
  rw [hu, DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]



/--
Importance-sampled generalized advantage estimation (Schulman et al., arXiv 1506.02438,
Eq. (16) with the importance-sampled score of Proposition 1) for continuous actions.
Sampling the action from a proposal parameter `θ'` replaces the on-policy score
`∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log` by
`(∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) / (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ)`,
provided `π_θ'` vanishes only where `π_θ` does. The state marginal stays the one
induced by `θ`.

`V` is the textbook (observation) form of the conditional expected return,
`V[t] «s»[t] = 𝔼[r: M θ]((γ ^ id) ⬝ᵥ r[t:] | s[t] = «s»[t])`. Path-GAE is the
functional of `(r, s)` built from `V[t + k] (s[t:] k)`, and `Â t x u` is defined
by evaluating the regular conditional of that functional:
`Â t x u = 𝔼[path-GAE(V) | s[t] = x ∧ a[t] = u]`. This is a version of
`𝔼[path-GAE(V) | s[t], a[t]]`, so `Â t s[t] a[t] =ᵐ[M θ] 𝔼[path-GAE(V) | s[t], a[t]]`.

With TD residuals `δ[j] = r[j] + γ * V[j, s[j+1]] - V[j, s[j]]` and
`{γ, ℓ} ⊆ Ico 0 1`, that coefficient is
`(1 - ℓ) * ((ℓ ^ id) ⬝ᵥ fun k ↦ (γ ^ range(k+1)) ⬝ᵥ δ)`.

`M[x] θ'` is the action law `M.policy.kernel θ' x`.

- [on-policy continuous GAE](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_Integrable_Measure.GtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico)
- [importance-sampled advantage policy gradient](?module=Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.GtInftySup.A_Function.importance_sampling)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  [Nonempty 𝒜] [StandardBorelSpace 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ θ' : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → (ℝ × 𝒮 × 𝒜)) → ℝ}
  {s : ℕ ⇀ (ℕ → (ℝ × 𝒮 × 𝒜)) → 𝒮}
  {a : ℕ ⇀ (ℕ → (ℝ × 𝒮 × 𝒜)) → 𝒜}
  {V : ℕ ⇀ 𝒮 → ℝ}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (hfactor : DensityModel.IsConditionalProbability M r s a)
  (h₁ : ∀ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)))
  (h₂ : ∃ (g : 𝒮 → 𝒜 → ℝ),
    (∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
        g «\sf{s}»[t] «\sf{a}»[t]) ∧
    (∀ x, Integrable (g x) ReferenceMeasure.measure) ∧
    (sup[x] (∫ u, g x u ∂ReferenceMeasure.measure) < ∞))
  (hφ : StronglyMeasurable
    (fun ((s0, a0) : 𝒮 × 𝒜) => ∇[θ] (ℙ[M θ](a[0] = a0 | s[0] = s0) : ℝ).log))
  (hMs : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
    ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞)
  (hV : ∀ t («\sf{s}» : ℕ ⇀ 𝒮),
    V[t] «\sf{s}»[t] =
      𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = «\sf{s}»[t]))
  (hsup : ∀ x u, M.policy.prob θ' x u ≠ 0 ∨ M.policy.prob θ x u = 0) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    hfactor.htr.singlePSpace_as (haj := hfactor.haj) θ t
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_r t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_s t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(hfactor.htr.measurable_a t).aemeasurable⟩)
  have hμ : ∀ (x : 𝒮), (M[x] θ' : Measure 𝒜) =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ' x) := fun x => by
    have hmeas : Measurable (Function.uncurry (M.policy.dens θ')) :=
      M.policy.measurable_dens θ'
    change M.policy.kernel θ' x =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ' x)
    exact Kernel.withDensity_apply (Kernel.const 𝒮 (ReferenceMeasure.measure : Measure 𝒜))
      hmeas x
  have hdens : ∀ (x : 𝒮), Measurable (M.policy.dens θ' x) := fun x =>
    (M.policy.measurable_dens θ').comp (Measurable.prodMk measurable_const measurable_id)
  have : ∀ (x : 𝒮), PSpace (M[x] θ') (id : 𝒜 → 𝒜) := fun x =>
    { aemeasurable := measurable_id.aemeasurable }
  have : ∀ (x : 𝒮), SinglePSpace (M[x] θ') (id : 𝒜 → 𝒜) := fun x =>
    SinglePSpace.of.AEMeasurable.Distributed
      (hdens x)
      (by rw [Measure.map_id, hμ x])
      measurable_id.aemeasurable
  let : MeasurableSpace Θ := borel Θ
  let Â : ℕ → 𝒮 → 𝒜 → ℝ := fun t x u =>
    𝔼[r, s : M θ](
      (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
          fun j => V[t + j] (s[t:] j)))
      | s[t] = x ∧ a[t] = u)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        (Â t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
          (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ))) := by
-- proof
  intro hPas _ _ _ hμ hdens hPker hSPker _ Â
  have hGAE :=
  GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.Any_And_All_Integrable_Measure.GtInftySup.All_Differentiable_Prob.All_NeDens_0.All_Eq_JointDens.AbsContJointAS.AbsContStateMarginal.IsPolicyTrajectory.Subset_Ico
    (M := M) (θ := θ) (γ := γ) (ℓ := ℓ) (r := r) (s := s) (a := a)
    h₀ hfactor h₁ h₂ hφ hMs hV
  rw [hGAE]
  have hπeq : ∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ) =
        M.policy.prob θ «\sf{s}»[t] «\sf{a}»[t] := fun θ t sb ab =>
      (hfactor.factor θ t (sb t) (ab t)).symm
  have hdiff : ∀ x u, Differentiable ℝ (fun κ => M.policy.prob κ x u) := fun x u => by
    have hd := h₁ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
    convert hd using 1
    funext κ
    exact (hπeq κ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩).symm
  have hγ : γ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ₀ : ℓ ∈ Set.Ico 0 1 := h₀ (by simp)
  have h₁' : ∀ t, (· t) = (r t, s t, a t) := hfactor.htr.stage_eq
  have hφpol : StronglyMeasurable
      (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := by
    convert hφ using 1
    funext z
    refine congrArg (gradient · θ) ?_
    funext κ
    simp only [hπeq κ 0 ⟨fun _ => z.1⟩ ⟨fun _ => z.2⟩]
  have hÂm : ∀ t, StronglyMeasurable (fun z : 𝒮 × 𝒜 => Â t z.1 z.2) := fun t => by
    set RewardPath := ∀ _ : ℕ, ℝ
    set StatePath := ∀ _ : ℕ, 𝒮
    let G : Prod RewardPath StatePath → ℝ := fun integ =>
      let r : Fun ℕ ℝ := ⟨integ.1⟩
      let s : Fun ℕ 𝒮 := ⟨integ.2⟩
      (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • (fun k ↦ V[t + 1 + k] (s[t + 1:] k)) -
          fun k ↦ V[t + k] (s[t:] k)))
    have hAeq : (fun z : 𝒮 × 𝒜 => Â t z.1 z.2) =
        (fun z => Expectation.condEval (M θ)
          (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
          (JointRandomSymbol (s.toFun t) (a.toFun t)) G z) := by
      funext z
      simp only [Â]
      dsimp only [G]
    have hres_eq : ∀ (p : Prod RewardPath StatePath) (k : ℕ),
        (let r : Fun ℕ ℝ := ⟨p.1⟩
          let s : Fun ℕ 𝒮 := ⟨p.2⟩
          r[t:] + γ • (fun k ↦ V[t + 1 + k] (s[t + 1:] k)) -
            fun k ↦ V[t + k] (s[t:] k)) k =
        p.1 (t + k) + γ * V[t + 1 + k] (p.2 (t + 1 + k)) - V[t + k] (p.2 (t + k)) := by
      intro p k
      simp only [Fun.getSliceFrom, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hres : Measurable
        (fun p : Prod RewardPath StatePath => fun k =>
          p.1 (t + k) + γ * V[t + 1 + k] (p.2 (t + 1 + k)) - V[t + k] (p.2 (t + k))) :=
      Measurable.of_eval fun k =>
        (((measurable_pi_apply (t + k)).comp measurable_fst).add
          (((measurable_of_countable (V[t + 1 + k])).comp
              ((measurable_pi_apply (t + 1 + k)).comp measurable_snd)).const_mul γ)).sub
          ((measurable_of_countable (V[t + k])).comp
            ((measurable_pi_apply (t + k)).comp measurable_snd))
    have hinner : Measurable
        (fun residual : RewardPath => fun k =>
          ∑ i ∈ range (k + 1), γ ^ i * residual i) :=
      Measurable.of_eval fun k =>
        Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
    have houter : Measurable
        (fun residual : RewardPath =>
          (ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun k => ∑ i ∈ range (k + 1), γ ^ i * residual i)) :=
      (Measurable.tsum fun k => (measurable_pi_apply k).const_mul _).comp hinner
    have hGeq : G =
        (fun p : Prod RewardPath StatePath =>
          (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ
            (fun k => ∑ i ∈ range (k + 1), γ ^ i *
              (p.1 (t + i) + γ * V[t + 1 + i] (p.2 (t + 1 + i)) -
                V[t + i] (p.2 (t + i)))))) := by
      funext p
      simp only [G, FinsetPow.dot_eq]
      refine congrArg (fun residual : RewardPath => (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ residual)) ?_
      funext k
      refine Finset.sum_congr rfl fun i _ => ?_
      exact congrArg (fun x => γ ^ i * x) (hres_eq p i)
    have hG : Measurable G := by
      rw [hGeq]
      apply Measurable.const_mul
      exact houter.comp hres
    have hGsm : StronglyMeasurable G := hG.stronglyMeasurable
    have hinteq :
        (fun z => Expectation.condEval (M θ)
          (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
          (JointRandomSymbol (s.toFun t) (a.toFun t)) G z) =
        (fun z => ∫ y, G y ∂(ProbabilityTheory.condDistrib
          (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
          (JointRandomSymbol (s.toFun t) (a.toFun t)) (M θ) z)) := by
      funext z
      unfold Expectation.condEval
      rw [expectation_real]
    rw [hAeq, hinteq]
    exact StronglyMeasurable.integral_kernel
      (κ := ProbabilityTheory.condDistrib
        (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
        (JointRandomSymbol (s.toFun t) (a.toFun t)) (M θ))
      hGsm
  -- For each state `x`, rewrite the IS inner expectation in policy densities,
  -- then apply `is_weight_eq_score`.
  have hIS : ∀ (t : ℕ) (x : 𝒮),
      Expectation.ofRV (M[x] θ') (id : 𝒜 → 𝒜)
        (fun u => (Â t x u • ∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u) =
        ∫ u, M.policy.prob θ x u • (Â t x u • ∇[θ] Real.log (M.policy.prob θ x u))
          ∂(ReferenceMeasure.measure : Measure 𝒜) := by
    intro t x
    have hP : PSpace (M[x] θ') (id : 𝒜 → 𝒜) := hPker x
    have hSP : SinglePSpace (M[x] θ') (id : 𝒜 → 𝒜) := hSPker x
    let fπ : 𝒜 → Θ := fun u =>
      (Â t x u • ∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u
    have hsm : AEStronglyMeasurable fπ ((M[x] θ').map (id : 𝒜 → 𝒜)) := by
      rw [Measure.map_id]
      have hx : Measurable (fun u : 𝒜 => (x, u)) :=
        Measurable.prodMk measurable_const measurable_id
      have hA : StronglyMeasurable (fun u : 𝒜 => Â t x u) :=
        (hÂm t).comp_measurable hx
      have hlog : StronglyMeasurable (fun u : 𝒜 => ∇[θ] Real.log (M.policy.prob θ x u)) :=
        hφpol.comp_measurable hx
      have hπ : Measurable (fun u : 𝒜 => M.policy.prob θ x u) :=
        (M.policy.measurable_prob θ).comp hx
      have hπ' : Measurable (fun u : 𝒜 => M.policy.prob θ' x u) :=
        (M.policy.measurable_prob θ').comp hx
      have hgrad_eq : ∀ u,
          ∇[θ] (M.policy.prob θ x u) =
            M.policy.prob θ x u • ∇[θ] Real.log (M.policy.prob θ x u) := fun u => by
        have hfd := smul_fderiv_log (M := M) hdiff θ x u
        simp only [gradient]
        rw [← hfd, map_smul]
      have hgrad : StronglyMeasurable (fun u : 𝒜 => ∇[θ] (M.policy.prob θ x u)) := by
        convert hπ.stronglyMeasurable.smul hlog using 1
        funext u
        exact hgrad_eq u
      have hnum : StronglyMeasurable
          (fun u : 𝒜 => Â t x u • ∇[θ] (M.policy.prob θ x u)) :=
        hA.smul hgrad
      have hf : StronglyMeasurable fπ := by
        convert (hπ'.inv.stronglyMeasurable.smul hnum) using 1
      exact hf.aestronglyMeasurable
    rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map (E := Θ) hsm]
    simp only [id]
    rw [integral_kernel (M := M) (f := fπ) θ' x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    exact is_weight_eq_score (M := M) (θ := θ) (θ' := θ') hdiff hsup x u (Â t x u)
  obtain ⟨Ms, hMsUB⟩ := hMs
  let : BorelSpace Θ := ⟨rfl⟩
  have hμθ : ∀ (x : 𝒮), (M[x] θ : Measure 𝒜) =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ x) := fun x => by
    have hmeas : Measurable (Function.uncurry (M.policy.dens θ)) :=
      M.policy.measurable_dens θ
    change M.policy.kernel θ x =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ x)
    exact Kernel.withDensity_apply (Kernel.const 𝒮 (ReferenceMeasure.measure : Measure 𝒜))
      hmeas x
  have hdensθ : ∀ (x : 𝒮), Measurable (M.policy.dens θ x) := fun x =>
    (M.policy.measurable_dens θ).comp (Measurable.prodMk measurable_const measurable_id)
  have hrω : ∀ t ω, r t ω = (ω t).1 := fun t ω =>
    (congrArg Prod.fst (congrFun (h₁' t) ω)).symm
  have hsω : ∀ t ω, s t ω = (ω t).2.1 := fun t ω =>
    (congrArg (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) (congrFun (h₁' t) ω)).symm
  have haω : ∀ t ω, a t ω = (ω t).2.2 := fun t ω =>
    (congrArg (fun z : ℝ × 𝒮 × 𝒜 => z.2.2) (congrFun (h₁' t) ω)).symm
  have hscore_bd : ∀ (x : 𝒮) (u : 𝒜),
      ‖∇[θ] Real.log (M.policy.prob θ x u)‖ ≤ Ms := fun x u => by
    have h := hMsUB (Set.mem_range_self (⟨fun _ => x⟩, ⟨fun _ => u⟩))
    have hfe :
        ∇[θ] Real.log (M.policy.prob θ x u) =
          ∇[θ] (ℙ[M θ](a[0] = u | s[0] = x) : ℝ).log := by
      refine congrArg (gradient · θ) ?_
      funext κ
      simp only [hπeq κ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩]
    rw [hfe]
    exact h
  have hrm : ∀ n, Measurable (r n) := fun n =>
    Random.Measurable.of.All_Eq.fst h₁' n
  have hsm : ∀ n, Measurable (s n) := fun n =>
    Random.Measurable.of.All_Eq.snd.fst h₁' n
  have ham : ∀ n, Measurable (a n) := fun n =>
    Random.Measurable.of.All_Eq.snd.snd h₁' n
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hsa : ∀ t, Measurable (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω)) := fun t =>
    (hsm t).prodMk (ham t)
  have hMs0 : 0 ≤ Ms := by
    inhabit 𝒮
    inhabit 𝒜
    exact le_trans (norm_nonneg _) (hscore_bd default default)
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hclip : ∀ j,
        r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity (M := M) h₁' θ j
    have hclip' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hclip
    filter_upwards [hclip'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hfG : ∀ n, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) := fun n =>
    Measurable.tsum fun k => (measurable_pi_apply (n + k)).const_mul _
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ n,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:])‖ ≤
        (1 - γ)⁻¹ * |M.env.R| := by
    have hgeo := (hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω n
    refine tsum_of_norm_bounded hgeo fun k => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) k = γ ^ k := rfl
    have hslice : (fun j => r j ω)[n:] k = r (n + k) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg hγ.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (n + k)) (pow_nonneg hγ.1 k)
  have hret : ∀ n, Measurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:] := fun n =>
    (hfG n).comp hpR
  have hGi : ∀ n,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[n:]) (M θ) :=
    fun n =>
      Integrable.of_bound (hret n).aestronglyMeasurable
        ((1 - γ)⁻¹ * |M.env.R|)
        (by filter_upwards [hret_bd] with ω hω; exact hω n)
  have hV_ae : ∀ n,
      (fun ω => V[n] (s n ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) := fun n => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s n)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:])
        hpR.aemeasurable (hsm n) (hfG n).stronglyMeasurable (hGi n)
    filter_upwards [hcomp] with ω hω
    have hx := hV n ⟨fun _ => s n ω⟩
    simp only at hx hω ⊢
    exact hx.trans hω
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ n, |V[n] (s n ω)| ≤ (1 - γ)⁻¹ * |M.env.R| := by
    have hcond : ∀ n, ∀ᵐ ω ∂(M θ),
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s n)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[n:]) ω| ≤
          (1 - γ)⁻¹ * |M.env.R| := fun n => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[n:])
          (m := MeasurableSpace.comap (s n) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω n)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm n
    rw [heq n]
    exact hnorm n
  have hbdd : ∀ᵐ ω ∂(M θ),
      BddAbove (Set.range fun j =>
        |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)|) := by
    filter_upwards [hr_bd, hVbd] with ω hr hV
    refine ⟨(2 / (1 - γ)) * |M.env.R|, ?_⟩
    rintro _ ⟨j, rfl⟩
    have hγn : 0 ≤ γ := hγ.1
    have htri :
        |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
          |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
      calc
        _ ≤ |r j ω + γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (r j ω + γ * V[j + 1] (s (j + 1) ω)) (-V[j] (s j ω))
        _ ≤ |r j ω| + |γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          rw [abs_mul, abs_of_nonneg hγn]
    have hle :=
      (add_le_add (add_le_add (hr j)
        (mul_le_mul_of_nonneg_left (hV (j + 1)) hγn)) (hV j))
    have hsum :
        |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) + (1 - γ)⁻¹ * |M.env.R| =
          (2 / (1 - γ)) * |M.env.R| := by
      have hne : 1 - γ ≠ 0 := sub_ne_zero.mpr hγ.2.ne.symm
      field_simp [hne]
      ring_nf
    exact (htri.trans hle).trans (le_of_eq hsum)
  have hpt : ∀ᵐ ω ∂(M θ), ∀ t,
    (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω))) =
    ((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
      (fun k : ℕ => r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
        V[t + k] (s (t + k) ω)) := by
    filter_upwards [hbdd] with ω hb t
    exact MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
      (δ := ⟨fun j => r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)⟩) (t := t) h₀ hb
  have hδbd : ∀ᵐ ω ∂(M θ), ∀ j,
      |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
        (2 / (1 - γ)) * |M.env.R| := by
    filter_upwards [hr_bd, hVbd] with ω hr hV j
    have hγn : 0 ≤ γ := hγ.1
    have htri :
        |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
          |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
      calc
        _ ≤ |r j ω + γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (r j ω + γ * V[j + 1] (s (j + 1) ω)) (-V[j] (s j ω))
        _ ≤ |r j ω| + |γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = |r j ω| + γ * |V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
          rw [abs_mul, abs_of_nonneg hγn]
    have hle :=
      (add_le_add (add_le_add (hr j)
        (mul_le_mul_of_nonneg_left (hV (j + 1)) hγn)) (hV j))
    have hsum :
        |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) + (1 - γ)⁻¹ * |M.env.R| =
          (2 / (1 - γ)) * |M.env.R| := by
      have hne : 1 - γ ≠ 0 := sub_ne_zero.mpr hγ.2.ne.symm
      field_simp [hne]
      ring_nf
    exact (htri.trans hle).trans (le_of_eq hsum)
  have hG_bd : ∀ᵐ ω ∂(M θ), ∀ t,
      |(1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω)))| ≤
        ((1 - γ * ℓ)⁻¹ * ((2 / (1 - γ)) * |M.env.R|)) := by
    have hγℓ : γ * ℓ < 1 := by
      have : γ * ℓ ≤ γ * 1 := mul_le_mul_of_nonneg_left hℓ₀.2.le hγ.1
      exact (this.trans_eq (mul_one γ)).trans_lt hγ.2
    have hgeo :=
      (hasSum_geometric_of_lt_one (mul_nonneg hγ.1 hℓ₀.1) hγℓ).mul_right
        ((2 / (1 - γ)) * |M.env.R|)
    filter_upwards [hpt, hδbd] with ω hι hδ t
    have habs :
        |((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
          (fun k : ℕ => r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
            V[t + k] (s (t + k) ω))| ≤
          (1 - γ * ℓ)⁻¹ * ((2 / (1 - γ)) * |M.env.R|) := by
      rw [← Real.norm_eq_abs]
      refine tsum_of_norm_bounded hgeo fun k => ?_
      have hid : ((γ * ℓ) ^ (id : ℕ → ℕ)) k = (γ * ℓ) ^ k := rfl
      rw [hid, norm_mul, norm_pow, Real.norm_of_nonneg (mul_nonneg hγ.1 hℓ₀.1),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hδ (t + k)) (pow_nonneg (mul_nonneg hγ.1 hℓ₀.1) k)
    rw [hι t]
    exact habs
  set BG : ℝ := (1 - γ * ℓ)⁻¹ * ((2 / (1 - γ)) * |M.env.R|)
  have hBG0 : 0 ≤ BG := by
    have hγℓ : γ * ℓ < 1 := by
      have : γ * ℓ ≤ γ * 1 := mul_le_mul_of_nonneg_left hℓ₀.2.le hγ.1
      exact (this.trans_eq (mul_one γ)).trans_lt hγ.2
    have hden : 0 ≤ (1 - γ * ℓ)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hγℓ.le)
    exact mul_nonneg hden (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sub_nonneg.mpr hγ.2.le)) (abs_nonneg _))
  let Gfun : ℕ → (ℕ → (ℝ × 𝒮 × 𝒜)) → ℝ := fun t ω =>
    (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) ω + γ * V[t + 1 + i] (s (t + 1 + i) ω) - V[t + i] (s (t + i) ω)))
  have hG_cast : ∀ t ω, Gfun t ω =
      (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V[t + i + 1] (s (t + i + 1) ω) - V[t + i] (s (t + i) ω))) := by
    intro t ω
    have hk : ∀ i, t + 1 + i = t + i + 1 := fun i => by omega
    simp only [Gfun, Nat.cast_one]
    congr 1
    congr 1
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hk i]
  have hG_ae : ∀ᵐ ω ∂(M θ), ∀ t, |Gfun t ω| ≤ BG := by
    filter_upwards [hG_bd] with ω h t
    rw [hG_cast t ω]
    exact h t
  have hGm : ∀ t, Measurable (Gfun t) := fun t => by
    have hres : Measurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => fun k =>
        r (t + k) ω + γ * V[t + 1 + k] (s (t + 1 + k) ω) - V[t + k] (s (t + k) ω) :=
      Measurable.of_eval fun k =>
        ((hrm (t + k)).add
          (((measurable_of_countable (V[t + 1 + k])).comp
            (hsm (t + 1 + k))).const_mul γ)).sub
          ((measurable_of_countable (V[t + k])).comp (hsm (t + k)))
    have hinner : Measurable fun residual : (ℕ → ℝ) => fun k =>
        ∑ i ∈ range (k + 1), γ ^ i * residual i :=
      Measurable.of_eval fun k =>
        Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
    have houter : Measurable fun residual : (ℕ → ℝ) =>
        (ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun k => ∑ i ∈ range (k + 1), γ ^ i * residual i) :=
      (Measurable.tsum fun k => (measurable_pi_apply k).const_mul _).comp hinner
    exact (houter.comp hres).const_mul _
  have hGiG : ∀ t, Integrable (Gfun t) (M θ) := fun t =>
    Integrable.of_bound (hGm t).aestronglyMeasurable BG
      (by filter_upwards [hG_ae] with ω h; exact h t)
  have hψbd : ∀ t ω,
      ‖∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))‖ ≤ Ms := fun t ω =>
    hscore_bd (s t ω) (a t ω)
  have hψm : ∀ t, Measurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) =>
      ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) := fun t =>
    hφpol.measurable.comp (hsa t)
  have hGψ : ∀ t, Integrable
      (fun ω => Gfun t ω • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))
      (M θ) := fun t =>
    Integrable.of_bound
      ((hGm t).stronglyMeasurable.smul (hψm t).stronglyMeasurable).aestronglyMeasurable
      (BG * Ms)
      (by
        filter_upwards [hG_ae] with ω h
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (h t) (hψbd t ω) (norm_nonneg _) hBG0)
  have hGω : ∀ t ω,
      (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) =>
        let r : Fun ℕ ℝ := ⟨integ.1⟩
        let s : Fun ℕ 𝒮 := ⟨integ.2⟩
        (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
          (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
            fun j => V[t + j] (s[t:] j))))
        (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s) ω) =
      Gfun t ω := fun t ω => by
    simp only [Gfun, JointRandomSymbol, Expectation.asRV,
      FinsetPow.dot_eq, Fun.getSliceFrom, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rfl
  have hGpath : ∀ t, StronglyMeasurable
      (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) =>
        let r : Fun ℕ ℝ := ⟨integ.1⟩
        let s : Fun ℕ 𝒮 := ⟨integ.2⟩
        (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
          (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
            fun j => V[t + j] (s[t:] j)))) := fun t => by
    have hres : Measurable
        (fun p : (ℕ → ℝ) × (ℕ → 𝒮) => fun k =>
          p.1 (t + k) + γ * V[t + 1 + k] (p.2 (t + 1 + k)) - V[t + k] (p.2 (t + k))) :=
      Measurable.of_eval fun k =>
        (((measurable_pi_apply (t + k)).comp measurable_fst).add
          (((measurable_of_countable (V[t + 1 + k])).comp
              ((measurable_pi_apply (t + 1 + k)).comp measurable_snd)).const_mul γ)).sub
          ((measurable_of_countable (V[t + k])).comp
            ((measurable_pi_apply (t + k)).comp measurable_snd))
    have hinner : Measurable
        (fun residual : (ℕ → ℝ) => fun k =>
          ∑ i ∈ range (k + 1), γ ^ i * residual i) :=
      Measurable.of_eval fun k =>
        Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _
    have houter : Measurable
        (fun residual : (ℕ → ℝ) =>
          (ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun k => ∑ i ∈ range (k + 1), γ ^ i * residual i)) :=
      (Measurable.tsum fun k => (measurable_pi_apply k).const_mul _).comp hinner
    refine ((houter.comp hres).const_mul _).stronglyMeasurable
  have hÂae : ∀ t,
      (fun ω => Â t (s t ω) (a t ω)) =ᵐ[M θ] Expectation.condSigma (M θ)
        (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
        (JointRandomSymbol (s.toFun t) (a.toFun t))
        (fun integ =>
          let r : Fun ℕ ℝ := ⟨integ.1⟩
          let s : Fun ℕ 𝒮 := ⟨integ.2⟩
          (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
            (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
              fun j => V[t + j] (s[t:] j)))) := fun t => by
    have hx : AEMeasurable
        (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s)) (M θ) :=
      PSpace.aemeasurable
    have hy : Measurable (JointRandomSymbol (s.toFun t) (a.toFun t)) :=
      (hsm t).prodMk (ham t)
    have hint : Integrable
        (fun ω =>
          (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) =>
            let r : Fun ℕ ℝ := ⟨integ.1⟩
            let s : Fun ℕ 𝒮 := ⟨integ.2⟩
            (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
              (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
                fun j => V[t + j] (s[t:] j))))
          (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s) ω)) (M θ) :=
      (hGiG t).congr (Eventually.of_forall fun ω => (hGω t ω).symm)
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
        (y := JointRandomSymbol (s.toFun t) (a.toFun t))
        (f := fun integ =>
          let r : Fun ℕ ℝ := ⟨integ.1⟩
          let s : Fun ℕ 𝒮 := ⟨integ.2⟩
          (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
            (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
              fun j => V[t + j] (s[t:] j))))
        hx hy (hGpath t) hint
    filter_upwards [hcomp] with ω hω
    exact hω
  have hσeq : ∀ t,
      Expectation.condSigma (M θ)
        (JointRandomSymbol (Expectation.asRV r) (Expectation.asRV s))
        (JointRandomSymbol (s.toFun t) (a.toFun t))
        (fun integ =>
          let r : Fun ℕ ℝ := ⟨integ.1⟩
          let s : Fun ℕ 𝒮 := ⟨integ.2⟩
          (↑1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
            (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
              fun j => V[t + j] (s[t:] j)))) =ᵐ[M θ]
      condExp (MeasurableSpace.comap
        (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
        (inferInstance : MeasurableSpace (𝒮 × 𝒜)))
        (M θ) (Gfun t) := fun t => by
    unfold Expectation.condSigma
    exact condExp_congr_ae (Eventually.of_forall fun ω => (hGω t ω).symm)
  have hÂbd : ∀ t, ∀ᵐ ω ∂(M θ), abs (Â t (s t ω) (a t ω)) ≤ BG := fun t => by
    have hce :=
      ae_bdd_norm_condExp_of_ae_bdd_norm
        (f := Gfun t)
        (m := MeasurableSpace.comap
          (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
          (inferInstance : MeasurableSpace (𝒮 × 𝒜)))
        (by filter_upwards [hG_ae] with ω h; exact h t)
    filter_upwards [hÂae t, hσeq t, hce] with ω hA hσ hC
    rw [hA, hσ]
    simpa [Real.norm_eq_abs] using hC
  let Âc : ℕ → 𝒮 → 𝒜 → ℝ := fun t x u => clip (Â t x u) (-BG) BG
  have hclip_ae : ∀ t, (fun ω => Âc t (s t ω) (a t ω)) =ᵐ[M θ]
      fun ω => Â t (s t ω) (a t ω) := fun t => by
    filter_upwards [hÂbd t] with ω h
    have hlo : -BG ≤ Â t (s t ω) (a t ω) := (abs_le.mp h).1
    have hhi : Â t (s t ω) (a t ω) ≤ BG := (abs_le.mp h).2
    change clip (Â t (s t ω) (a t ω)) (-BG) BG = Â t (s t ω) (a t ω)
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have hÂc_bd : ∀ t x u, abs (Âc t x u) ≤ BG := fun t x u => by
    have hlo : -BG ≤ clip (Â t x u) (-BG) BG :=
      le_min (le_max_right _ _) (neg_le_self hBG0)
    have hhi : clip (Â t x u) (-BG) BG ≤ BG := min_le_right _ _
    exact abs_le.mpr ⟨hlo, hhi⟩
  have hcont : Continuous fun x : ℝ => clip x (-BG) BG := by
    unfold clip
    exact (continuous_id.max continuous_const).min continuous_const
  have hφsm : ∀ t, StronglyMeasurable
      (Function.uncurry fun y u =>
        Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u)) := fun t => by
    have hA : StronglyMeasurable (fun z : 𝒮 × 𝒜 => Âc t z.1 z.2) :=
      (hcont.measurable.comp (hÂm t).measurable).stronglyMeasurable
    exact hA.smul hφpol
  have hCφ : ∀ t y u,
      ‖Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ BG * Ms := fun t y u => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hÂc_bd t y u) (hscore_bd y u) (norm_nonneg _) hBG0
  have hdis : ∀ t,
      ∫ ω, Âc t (s t ω) (a t ω) • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∫ y, (∫ u, M.policy.prob θ y u •
            (Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u))
          ∂ReferenceMeasure.measure) ∂((M θ).map (s t)) := fun t =>
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) (φ := fun y u => Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u))
      (C := BG * Ms) h₁' (hφsm t) (hCφ t) θ t
  have hscore_m : ∀ t,
      StronglyMeasurable[MeasurableSpace.comap
        (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
        (inferInstance : MeasurableSpace (𝒮 × 𝒜))]
      (fun ω => ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) := fun t =>
    hφpol.comp_measurable (Measurable.of_comap_le le_rfl)
  have htower : ∀ t,
      ∫ ω, Gfun t ω • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∫ ω, Â t (s t ω) (a t ω) •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) := fun t => by
    have hm : MeasurableSpace.comap
        (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
        (inferInstance : MeasurableSpace (𝒮 × 𝒜)) ≤
        (inferInstance : MeasurableSpace (ℕ → (ℝ × 𝒮 × 𝒜))) :=
      (hsa t).comap_le
    set ψ : (ℕ → (ℝ × 𝒮 × 𝒜)) → Θ :=
      fun ω => ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))
    have hsmul_eq : (fun ω => Gfun t ω • ψ ω) = fun ω => (Gfun t • ψ) ω := by
      funext ω
      rfl
    have hGψPi : Integrable (Gfun t • ψ) (M θ) :=
      (hGψ t).congr (Eventually.of_forall fun ω => (hsmul_eq ▸ rfl))
    have hpull :=
      condExp_smul_of_aestronglyMeasurable_right
        (f := Gfun t) (g := ψ)
        (m := MeasurableSpace.comap
          (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
          (inferInstance : MeasurableSpace (𝒮 × 𝒜)))
        (hGiG t) hGψPi (hscore_m t).aestronglyMeasurable
    have : SigmaFinite ((M θ).trim hm) := inferInstance
    have hre : ∫ ω, Gfun t ω • ψ ω ∂(M θ) = ∫ ω, (Gfun t • ψ) ω ∂(M θ) :=
      integral_congr_ae (Eventually.of_forall fun ω => hsmul_eq ▸ rfl)
    rw [hre, ← integral_condExp hm (f := Gfun t • ψ)]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hÂae t, hσeq t] with ω hω hA hσ
    rw [hω]
    change condExp (MeasurableSpace.comap
          (fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => (s t ω, a t ω))
          (inferInstance : MeasurableSpace (𝒮 × 𝒜)))
          (M θ) (Gfun t) ω • ψ ω =
      Â t (s t ω) (a t ω) • ψ ω
    rw [← hσ, hA]
  have hÂ_eq_clip : ∀ t,
      ∫ ω, Â t (s t ω) (a t ω) •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∫ ω, Âc t (s t ω) (a t ω) •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) := fun t =>
    integral_congr_ae (by
      filter_upwards [hclip_ae t] with ω h
      rw [h])
  have hinner_clip : ∀ t, ∀ᵐ y ∂((M θ).map (s t)),
      ∫ u, M.policy.prob θ y u • (Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u))
        ∂ReferenceMeasure.measure =
      Expectation.ofRV (M[y] θ') (id : 𝒜 → 𝒜)
        (fun u => (Â t y u • ∇[θ] (M.policy.prob θ y u)) /
          M.policy.prob θ' y u) := fun t => by
    have hbad : ∫ ω,
        (if abs (Â t (s t ω) (a t ω)) ≤ BG then (0 : ℝ) else 1) ∂(M θ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hÂbd t] with ω h
      simp [h]
    have hφind : StronglyMeasurable
        (Function.uncurry fun y u =>
          (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)) := by
      have hA : Measurable (fun z : 𝒮 × 𝒜 => Â t z.1 z.2) := (hÂm t).measurable
      have hset : MeasurableSet {z : 𝒮 × 𝒜 | abs (Â t z.1 z.2) ≤ BG} := by
        have hEq : {z : 𝒮 × 𝒜 | abs (Â t z.1 z.2) ≤ BG} =
            (fun z : 𝒮 × 𝒜 => Â t z.1 z.2) ⁻¹' Set.Icc (-BG) BG := by
          ext z; simp [abs_le, Set.mem_preimage, Set.mem_Icc]
        rw [hEq]
        exact hA measurableSet_Icc
      exact (measurable_const.ite hset measurable_const).stronglyMeasurable
    have hdis0 :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) (E := ℝ)
        (φ := fun y u => if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
        (C := (1 : ℝ)) h₁' hφind (fun y u => by
          by_cases h : abs (Â t y u) ≤ BG <;> simp [h]) θ t
    have hinter0 :
        ∫ y, (∫ u, M.policy.prob θ y u •
            (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
          ∂ReferenceMeasure.measure) ∂((M θ).map (s t)) = 0 := by
      simpa [hbad] using hdis0.symm
    have hnn : ∀ y,
        0 ≤ ∫ u, M.policy.prob θ y u •
          (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
          ∂ReferenceMeasure.measure := fun y =>
      integral_nonneg fun u =>
        mul_nonneg (M.policy.nonneg θ y u) (by by_cases h : abs (Â t y u) ≤ BG <;> simp [h])
    have hy0 : ∀ᵐ y ∂((M θ).map (s t)),
        ∫ u, M.policy.prob θ y u •
          (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
          ∂ReferenceMeasure.measure = 0 := by
      have hintg : Integrable
          (fun y => ∫ u, M.policy.prob θ y u •
            (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
            ∂ReferenceMeasure.measure) ((M θ).map (s t)) := by
        have hfite : StronglyMeasurable
            (Function.uncurry fun (y : 𝒮) (u : 𝒜) =>
              M.policy.prob θ y u *
                (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)) :=
          ((M.policy.measurable_prob θ).mul hφind.measurable).stronglyMeasurable
        have hsmY' : StronglyMeasurable
            (fun y => ∫ u, M.policy.prob θ y u •
              (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
              ∂ReferenceMeasure.measure) := by
          have h :=
            hfite.integral_prod_right (ν := (ReferenceMeasure.measure : Measure 𝒜))
          exact h
        refine Integrable.of_bound hsmY'.aestronglyMeasurable 1 ?_
        refine Eventually.of_forall fun y => ?_
        have hrew := integral_kernel (M := M)
          (f := fun u => if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) θ y
        have hle :
            ∫ u, (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) ∂(M[y] θ) ≤
              ∫ u, (1 : ℝ) ∂(M[y] θ) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun u => by
              by_cases h : abs (Â t y u) ≤ BG <;> simp [h])
            (integrable_const (1 : ℝ))
            (Eventually.of_forall fun u => by
              by_cases h : abs (Â t y u) ≤ BG <;> simp [h])
        have hone : ∫ u, (1 : ℝ) ∂(M[y] θ) = 1 := by
          have : IsProbabilityMeasure (M[y] θ : Measure 𝒜) := inferInstance
          simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
            smul_eq_mul]
        have hval :
            abs (∫ u, M.policy.prob θ y u •
              (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
              ∂ReferenceMeasure.measure) ≤ 1 := by
          rw [← hrew]
          have hnn' : 0 ≤ ∫ u, (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) ∂(M[y] θ) :=
            integral_nonneg fun u => by
              by_cases h : abs (Â t y u) ≤ BG <;> simp [h]
          rw [abs_of_nonneg hnn']
          exact hle.trans (le_of_eq hone)
        exact hval
      exact (integral_eq_zero_iff_of_nonneg hnn hintg).1 hinter0
    filter_upwards [hy0] with y hy
    have hu : ∀ᵐ u ∂(ReferenceMeasure.measure : Measure 𝒜),
        M.policy.prob θ y u = 0 ∨ abs (Â t y u) ≤ BG := by
      have hmul :
          ∫ u, M.policy.prob θ y u * (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1)
            ∂ReferenceMeasure.measure = 0 := by
        simpa [smul_eq_mul] using hy
      have hnn' : 0 ≤ fun u =>
          M.policy.prob θ y u * (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) := fun u =>
        mul_nonneg (M.policy.nonneg θ y u) (by by_cases h : abs (Â t y u) ≤ BG <;> simp [h])
      have hAμ : Measurable fun u : 𝒜 => Â t y u :=
        (hÂm t).measurable.comp (Measurable.prodMk measurable_const measurable_id)
      have hsetμ : MeasurableSet {u : 𝒜 | abs (Â t y u) ≤ BG} := by
        have hEq : {u : 𝒜 | abs (Â t y u) ≤ BG} =
            (fun u : 𝒜 => Â t y u) ⁻¹' Set.Icc (-BG) BG := by
          ext u; simp [abs_le, Set.mem_preimage, Set.mem_Icc]
        rw [hEq]
        exact hAμ measurableSet_Icc
      have hindμ : Measurable fun u : 𝒜 =>
          (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) :=
        measurable_const.ite hsetμ measurable_const
      have hπint : Integrable (M.policy.prob θ y) ReferenceMeasure.measure := by
        have h1 : Integrable (fun _ : 𝒜 => (1 : ℝ)) (M[y] θ) := integrable_const 1
        rw [hμθ y] at h1
        have h' :=
          (integrable_withDensity_iff (μ := ReferenceMeasure.measure)
            (f := M.policy.dens θ y) (hdensθ y)
            (Eventually.of_forall fun u => by
              simp [DensityPolicy.dens, ENNReal.ofReal_lt_top])).1 h1
        convert h' using 1
        funext u
        simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ y u)]
      have hprodint : Integrable
          (fun u => M.policy.prob θ y u *
            (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1))
          ReferenceMeasure.measure :=
        Integrable.mono' hπint
          (((M.policy.measurable_prob θ).comp
            (Measurable.prodMk measurable_const measurable_id)).mul hindμ).aestronglyMeasurable
          (Eventually.of_forall fun u => by
            have hπ0 : 0 ≤ M.policy.prob θ y u := M.policy.nonneg θ y u
            by_cases h : abs (Â t y u) ≤ BG <;>
              simp [h, abs_of_nonneg hπ0, hπ0])
      have hz :=
        (integral_eq_zero_iff_of_nonneg hnn' hprodint).1 (by simpa using hmul)
      filter_upwards [hz] with u hu
      by_cases hπ0 : M.policy.prob θ y u = 0
      · exact Or.inl hπ0
      · refine Or.inr ?_
        by_contra hgt
        have hite : (if abs (Â t y u) ≤ BG then (0 : ℝ) else 1) = 1 := by
          simp [hgt]
        have : M.policy.prob θ y u * 1 = 0 := by simpa [hite] using hu
        exact hπ0 (by simpa using this)
    have := hIS t y
    refine Eq.trans ?_ this.symm
    refine integral_congr_ae ?_
    filter_upwards [hu] with u hu
    by_cases hp : M.policy.prob θ y u = 0
    · simp [hp, Âc]
    · have hle : abs (Â t y u) ≤ BG := hu.resolve_left hp
      have hlo : -BG ≤ Â t y u := (abs_le.mp hle).1
      have hhi : Â t y u ≤ BG := (abs_le.mp hle).2
      have hceq : Âc t y u = Â t y u := by
        change clip (Â t y u) (-BG) BG = Â t y u
        rw [clip, max_eq_left hlo, min_eq_left hhi]
      simp [hceq]
  have hterm : ∀ t,
      ∫ ω, Gfun t ω • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∫ y, Expectation.ofRV (M[y] θ') (id : 𝒜 → 𝒜)
          (fun u => (Â t y u • ∇[θ] (M.policy.prob θ y u)) /
            M.policy.prob θ' y u) ∂((M θ).map (s t)) := fun t =>
    ((htower t).trans (hÂ_eq_clip t)).trans ((hdis t).trans (integral_congr_ae (hinner_clip t)))
  have hφg : StronglyMeasurable
      (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := hφpol
  have hφgℙ : ∀ t, StronglyMeasurable fun z : 𝒮 × 𝒜 =>
      ∇[θ] (ℙ[M θ]((a t) = z.2 | (s t) = z.1) : ℝ).log := fun t => by
    convert hφg using 1
    funext z
    refine congrArg (gradient · θ) ?_
    funext κ
    simp only [hπeq κ t ⟨fun _ => z.1⟩ ⟨fun _ => z.2⟩]
  have hexp : ∀ F : ℕ → (ℕ → 𝒮) → (ℕ → 𝒜) → (ℕ → ℝ) → ℝ,
    (∀ t, Measurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
    𝔼[r, s, a : M θ](
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ (F t s a r •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) =
    ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        ((hφgℙ t).comp_measurable ((hsm t).prodMk (ham t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) =>
      ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜)) =>
      fun t => (p.1 t, p.2.1 t, p.2.2 t)
    have fromPath_meas : Measurable fromPath :=
      Measurable.of_eval fun t =>
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    · exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath, hrω, hsω, haω]
          rfl)
    simp only [JointRandomSymbol, hrω, hsω, haω]
    first | rfl | (congr 1; funext ω; simp [hrω, hsω, haω]; rfl)
  have hFGAE : ∀ t, Measurable fun ω : ℕ → (ℝ × 𝒮 × 𝒜) =>
      (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        ((fun j => r j ω)[t:] + γ • (fun j => V[t + 1 + j] ((fun j => s j ω)[t + 1:] j)) -
          fun j => V[t + j] ((fun j => s j ω)[t:] j))) := fun t => by
    convert (hGm t) using 1
    funext ω
    rw [hG_cast t ω]
    simp only [FinsetPow.dot_eq]
    congr 1
    congr 1
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Function.getSliceFrom_apply, Nat.add_right_comm t 1 i]
  have hLHS :=
    hexp (fun t s a r =>
      (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
          fun j => V[t + j] (s[t:] j)))) hFGAE
  have hsrc :
      (fun t (s : ℕ → 𝒮) (a : ℕ → 𝒜) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
          (r[t:] + γ • (⟨fun t δ k => V[t + k] (δ k)⟩ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ)[t + 1] s[t + 1:] -
            (⟨fun t δ k => V[t + k] (δ k)⟩ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ)[t] s[t:]))) =
      (fun t (s : ℕ → 𝒮) (a : ℕ → 𝒜) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
          (r[t:] + γ • (fun j => V[t + 1 + j] (s[t + 1:] j)) -
            fun j => V[t + j] (s[t:] j)))) := by
    funext t s a r
    rfl
  have hscore_eq : ∀ t ω,
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) := fun t ω => by
    refine congrArg (gradient · θ) ?_
    funext κ
    simp only [hπeq κ t ⟨fun _ => s t ω⟩ ⟨fun _ => a t ω⟩]
  let innerC : ℕ → 𝒮 → Θ := fun t y =>
    ∫ u, M.policy.prob θ y u • (Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u))
      ∂ReferenceMeasure.measure
  have hinnerC_m : ∀ t, StronglyMeasurable (innerC t) := fun t => by
    have hf : StronglyMeasurable
        (Function.uncurry fun (y : 𝒮) (u : 𝒜) =>
          M.policy.prob θ y u • (Âc t y u • ∇[θ] Real.log (M.policy.prob θ y u))) :=
      ((M.policy.measurable_prob θ).smul (hφsm t).measurable).stronglyMeasurable
    exact hf.integral_prod_right (ν := (ReferenceMeasure.measure : Measure 𝒜))
  have hπint : ∀ y, Integrable (M.policy.prob θ y) ReferenceMeasure.measure := fun y => by
    have h1 : Integrable (fun _ : 𝒜 => (1 : ℝ)) (M[y] θ) := integrable_const 1
    rw [hμθ y] at h1
    have h' :=
      (integrable_withDensity_iff (μ := ReferenceMeasure.measure)
        (f := M.policy.dens θ y) (hdensθ y)
        (Eventually.of_forall fun u => by
          simp [DensityPolicy.dens, ENNReal.ofReal_lt_top])).1 h1
    convert h' using 1
    funext u
    simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ y u)]
  have hπ1 : ∀ y, ∫ u, M.policy.prob θ y u ∂ReferenceMeasure.measure = 1 := fun y => by
    have hrew := integral_kernel (M := M) (f := fun _ : 𝒜 => (1 : ℝ)) θ y
    have : IsProbabilityMeasure (M[y] θ : Measure 𝒜) := inferInstance
    simpa [smul_eq_mul, integral_const, Measure.real, measure_univ, ENNReal.toReal_one] using hrew.symm
  have hinnerC_bd : ∀ t y, ‖innerC t y‖ ≤ BG * Ms := fun t y => by
    have hle :
        ‖innerC t y‖ ≤ ∫ u, M.policy.prob θ y u * (BG * Ms) ∂ReferenceMeasure.measure := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun _ => norm_nonneg _)
        ((hπint y).mul_const (BG * Ms))
        (Eventually.of_forall fun u => ?_)
      have hπ0 : 0 ≤ M.policy.prob θ y u := M.policy.nonneg θ y u
      change ‖M.policy.prob θ y u • (Âc t y u •
          ∇[θ] Real.log (M.policy.prob θ y u))‖ ≤
        M.policy.prob θ y u * (BG * Ms)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hπ0]
      exact mul_le_mul_of_nonneg_left (hCφ t y u) hπ0
    have hconst : ∫ u, M.policy.prob θ y u * (BG * Ms) ∂ReferenceMeasure.measure =
        BG * Ms := by
      have hmul :
          (fun u => M.policy.prob θ y u * (BG * Ms)) =
            fun u => M.policy.prob θ y u • (BG * Ms) := rfl
      rw [hmul, integral_smul_const, hπ1 y, smul_eq_mul, one_mul]
    exact hle.trans (le_of_eq hconst)
  have htermC : ∀ t,
      ∫ ω, Gfun t ω • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∫ y, innerC t y ∂((M θ).map (s t)) := fun t =>
    ((htower t).trans (hÂ_eq_clip t)).trans (hdis t)
  have hswap_G :
      ∫ ω, ∑' t, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) =
        ∑' t, γ ^ t • ∫ ω, Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) := by
    have hFsm : ∀ n, AEStronglyMeasurable
        (fun ω => ∑ t ∈ range n, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))) (M θ) := fun n =>
      (Finset.measurable_sum (range n) fun t _ =>
        (((hGm t).smul (hψm t)).const_smul (γ ^ t))).stronglyMeasurable.aestronglyMeasurable
    have hlimsm : AEStronglyMeasurable
        (fun ω => ∑' t, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))) (M θ) :=
      (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        ((hGm t).stronglyMeasurable.smul (hψm t).stronglyMeasurable).const_smul
          (γ ^ t)).aestronglyMeasurable
    have hbound_int : Integrable
        (fun _ : ℕ → (ℝ × 𝒮 × 𝒜) => (1 - γ)⁻¹ * (BG * Ms)) (M θ) :=
      integrable_const _
    have hbound' : ∀ n, ∀ᵐ ω ∂(M θ),
        ‖∑ t ∈ range n, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))‖ ≤
        (1 - γ)⁻¹ * (BG * Ms) := fun n => by
      filter_upwards [hG_ae] with ω hG
      refine (norm_sum_le _ _).trans ?_
      have hterm_le : ∀ t ∈ range n,
          ‖γ ^ t • (Gfun t ω • ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))‖ ≤
            γ ^ t * (BG * Ms) := fun t _ => by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg hγ.1 t)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hG t) (hψbd t ω) (norm_nonneg _) hBG0) (pow_nonneg hγ.1 t)
      refine (Finset.sum_le_sum hterm_le).trans ?_
      have hsum : ∑ t ∈ range n, γ ^ t * (BG * Ms) =
          (∑ t ∈ range n, γ ^ t) * (BG * Ms) := by
        simp [Finset.sum_mul]
      rw [hsum]
      have hgeo : ∑ t ∈ range n, γ ^ t ≤ (1 - γ)⁻¹ := by
        have hs : Summable fun t : ℕ => γ ^ t :=
          summable_geometric_of_lt_one hγ.1 hγ.2
        exact (hs.sum_le_tsum (range n) (fun _ _ => pow_nonneg hγ.1 _)).trans
          (le_of_eq (tsum_geometric_of_lt_one hγ.1 hγ.2))
      exact mul_le_mul_of_nonneg_right hgeo (mul_nonneg hBG0 hMs0)
    have hlim : ∀ᵐ ω ∂(M θ),
        Tendsto (fun n => ∑ t ∈ range n, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))) atTop
          (𝓝 (∑' t, γ ^ t • (Gfun t ω •
            ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))))) := by
      filter_upwards [hG_ae] with ω hG
      have hsum : Summable fun t : ℕ => γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
        have hg : Summable fun t : ℕ => γ ^ t * (BG * Ms) :=
          (summable_geometric_of_lt_one hγ.1 hγ.2).mul_right (BG * Ms)
        refine hg.of_norm_bounded fun t => by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hγ.1 t)]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (hG t) (hψbd t ω) (norm_nonneg _) hBG0) (pow_nonneg hγ.1 t)
      exact hsum.hasSum.tendsto_sum_nat
    have htendsto :=
      tendsto_integral_of_dominated_convergence
        (F := fun n ω => ∑ t ∈ range n, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))))
        (f := fun ω => ∑' t, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))))
        (bound := fun _ => (1 - γ)⁻¹ * (BG * Ms))
        (bound_integrable := hbound_int)
        (F_measurable := hFsm)
        (h_bound := hbound')
        (h_lim := hlim)
    have hpartial : ∀ n,
        ∫ ω, ∑ t ∈ range n, γ ^ t • (Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) =
          ∑ t ∈ range n, γ ^ t • ∫ ω, Gfun t ω •
            ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) := fun n => by
      have hint : ∀ t ∈ range n,
          Integrable (fun ω => γ ^ t • (Gfun t ω •
            ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)))) (M θ) :=
        fun t _ => Integrable.smul (γ ^ t) (hGψ t)
      rw [integral_finsetSum _ hint]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_smul]
    have hsum_int : Summable fun t : ℕ => γ ^ t • ∫ ω, Gfun t ω •
        ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) := by
      have hg : Summable fun t : ℕ => γ ^ t * (BG * Ms) :=
        (summable_geometric_of_lt_one hγ.1 hγ.2).mul_right (BG * Ms)
      refine hg.of_norm_bounded fun t => by
        have : ‖∫ ω, Gfun t ω •
            ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ)‖ ≤ BG * Ms := by
          refine (norm_integral_le_integral_norm _).trans ?_
          have : ∫ ω, ‖Gfun t ω •
              ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω))‖ ∂(M θ) ≤
              ∫ ω, BG * Ms ∂(M θ) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) ?_
            filter_upwards [hG_ae] with ω hG
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hG t) (hψbd t ω) (norm_nonneg _) hBG0
          have hone : ∫ ω, (BG * Ms : ℝ) ∂(M θ) = BG * Ms := by
            have : IsProbabilityMeasure (M θ : Measure (ℕ → (ℝ × 𝒮 × 𝒜))) := inferInstance
            rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
          exact this.trans (le_of_eq hone)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ.1 t)]
        exact mul_le_mul_of_nonneg_left this (pow_nonneg hγ.1 t)
    have htendsto_sum := hsum_int.hasSum.tendsto_sum_nat
    refine tendsto_nhds_unique htendsto ?_
    convert htendsto_sum using 1
    funext n
    exact hpartial n
  have hswap_C :
      ∑' t, γ ^ t • ∫ y, innerC t y ∂((M θ).map (s t)) =
        ∫ ω, ∑' t, γ ^ t • innerC t (s t ω) ∂(M θ) := by
    have hFsm : ∀ n, AEStronglyMeasurable
        (fun ω => ∑ t ∈ range n, γ ^ t • innerC t (s t ω)) (M θ) := fun n =>
      (Finset.measurable_sum (range n) fun t _ =>
        (((hinnerC_m t).measurable.comp (hsm t)).const_smul (γ ^ t))).stronglyMeasurable.aestronglyMeasurable
    have hlimsm : AEStronglyMeasurable
        (fun ω => ∑' t, γ ^ t • innerC t (s t ω)) (M θ) :=
      (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        ((hinnerC_m t).comp_measurable (hsm t)).const_smul (γ ^ t)).aestronglyMeasurable
    have hbound_int : Integrable
        (fun _ : ℕ → (ℝ × 𝒮 × 𝒜) => (1 - γ)⁻¹ * (BG * Ms)) (M θ) :=
      integrable_const _
    have hbound' : ∀ n, ∀ᵐ ω ∂(M θ),
        ‖∑ t ∈ range n, γ ^ t • innerC t (s t ω)‖ ≤
        (1 - γ)⁻¹ * (BG * Ms) := fun n =>
      Eventually.of_forall fun ω => by
        refine (norm_sum_le _ _).trans ?_
        have hterm_le : ∀ t ∈ range n,
            ‖γ ^ t • innerC t (s t ω)‖ ≤ γ ^ t * (BG * Ms) := fun t _ => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ.1 t)]
          exact mul_le_mul_of_nonneg_left (hinnerC_bd t (s t ω)) (pow_nonneg hγ.1 t)
        refine (Finset.sum_le_sum hterm_le).trans ?_
        have hsum : ∑ t ∈ range n, γ ^ t * (BG * Ms) =
            (∑ t ∈ range n, γ ^ t) * (BG * Ms) := by
          simp [Finset.sum_mul]
        rw [hsum]
        have hgeo : ∑ t ∈ range n, γ ^ t ≤ (1 - γ)⁻¹ := by
          have hs : Summable fun t : ℕ => γ ^ t :=
            summable_geometric_of_lt_one hγ.1 hγ.2
          exact (hs.sum_le_tsum (range n) (fun _ _ => pow_nonneg hγ.1 _)).trans
            (le_of_eq (tsum_geometric_of_lt_one hγ.1 hγ.2))
        exact mul_le_mul_of_nonneg_right hgeo (mul_nonneg hBG0 hMs0)
    have hlim : ∀ᵐ ω ∂(M θ),
        Tendsto (fun n => ∑ t ∈ range n, γ ^ t • innerC t (s t ω)) atTop
          (𝓝 (∑' t, γ ^ t • innerC t (s t ω))) :=
      Eventually.of_forall fun ω => by
        have hsum : Summable fun t : ℕ => γ ^ t • innerC t (s t ω) := by
          have hg : Summable fun t : ℕ => γ ^ t * (BG * Ms) :=
            (summable_geometric_of_lt_one hγ.1 hγ.2).mul_right (BG * Ms)
          refine hg.of_norm_bounded fun t => by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ.1 t)]
            exact mul_le_mul_of_nonneg_left (hinnerC_bd t (s t ω)) (pow_nonneg hγ.1 t)
        exact hsum.hasSum.tendsto_sum_nat
    have htendsto :=
      tendsto_integral_of_dominated_convergence
        (F := fun n ω => ∑ t ∈ range n, γ ^ t • innerC t (s t ω))
        (f := fun ω => ∑' t, γ ^ t • innerC t (s t ω))
        (bound := fun _ => (1 - γ)⁻¹ * (BG * Ms))
        (bound_integrable := hbound_int)
        (F_measurable := hFsm)
        (h_bound := hbound')
        (h_lim := hlim)
    have hint : ∀ t, Integrable (fun ω => γ ^ t • innerC t (s t ω)) (M θ) := fun t =>
      Integrable.of_bound
        (((hinnerC_m t).comp_measurable (hsm t)).const_smul (γ ^ t)).aestronglyMeasurable
        (γ ^ t * (BG * Ms))
        (Eventually.of_forall fun ω => by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ.1 t)]
          exact mul_le_mul_of_nonneg_left (hinnerC_bd t (s t ω)) (pow_nonneg hγ.1 t))
    have hpartial : ∀ n,
        ∫ ω, ∑ t ∈ range n, γ ^ t • innerC t (s t ω) ∂(M θ) =
          ∑ t ∈ range n, γ ^ t • ∫ y, innerC t y ∂((M θ).map (s t)) := fun n => by
      rw [integral_finsetSum _ (fun t _ => hint t)]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_smul, integral_map (hsm t).aemeasurable (hinnerC_m t).aestronglyMeasurable]
    have hsum_int : Summable fun t : ℕ =>
        γ ^ t • ∫ y, innerC t y ∂((M θ).map (s t)) := by
      have hg : Summable fun t : ℕ => γ ^ t * (BG * Ms) :=
        (summable_geometric_of_lt_one hγ.1 hγ.2).mul_right (BG * Ms)
      refine hg.of_norm_bounded fun t => by
        have : ‖∫ y, innerC t y ∂((M θ).map (s t))‖ ≤ BG * Ms := by
          refine (norm_integral_le_integral_norm _).trans ?_
          have : ∫ y, ‖innerC t y‖ ∂((M θ).map (s t)) ≤ ∫ y, BG * Ms ∂((M θ).map (s t)) :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _) (Eventually.of_forall fun y => hinnerC_bd t y)
          have hone : ∫ y, (BG * Ms : ℝ) ∂((M θ).map (s t)) = BG * Ms := by
            have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
            rw [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
          exact this.trans (le_of_eq hone)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hγ.1 t)]
        exact mul_le_mul_of_nonneg_left this (pow_nonneg hγ.1 t)
    have htendsto_sum := hsum_int.hasSum.tendsto_sum_nat
    refine Eq.symm (tendsto_nhds_unique htendsto ?_)
    convert htendsto_sum using 1
    funext n
    exact hpartial n
  have hC_ae : ∀ᵐ ω ∂(M θ), ∀ t,
      innerC t (s t ω) =
        Expectation.ofRV (M[s t ω] θ') (id : 𝒜 → 𝒜)
          (fun u => (Â t (s t ω) u • ∇[θ] (M.policy.prob θ (s t ω) u)) /
            M.policy.prob θ' (s t ω) u) := by
    have ht : ∀ t, ∀ᵐ ω ∂(M θ),
        innerC t (s t ω) =
          Expectation.ofRV (M[s t ω] θ') (id : 𝒜 → 𝒜)
            (fun u => (Â t (s t ω) u • ∇[θ] (M.policy.prob θ (s t ω) u)) /
              M.policy.prob θ' (s t ω) u) := fun t =>
      ae_of_ae_map (hsm t).aemeasurable (hinner_clip t)
    exact (ae_all_iff (ι := ℕ)).mpr ht
  have hRHS : 𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        (Â t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
          (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ))) =
      ∫ ω, ∑' t, γ ^ t • Expectation.ofRV (M[s t ω] θ') (id : 𝒜 → 𝒜)
        (fun u => (Â t (s t ω) u • ∇[θ] (M.policy.prob θ (s t ω) u)) /
          M.policy.prob θ' (s t ω) u) ∂(M θ) := by
    rw [Expectation.ofRV, expectation_bochner]
    dsimp
    have hx : AEMeasurable (Expectation.asRV s) (M θ) := PSpace.aemeasurable
    have hinner_path : AEStronglyMeasurable
        (fun σ : ℕ → 𝒮 => ∑' t, γ ^ t • innerC t (σ t))
        ((M θ).map (Expectation.asRV s)) :=
      (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        ((hinnerC_m t).comp_measurable (measurable_pi_apply t)).const_smul
          (γ ^ t)).aestronglyMeasurable
    have hpS : Measurable (Expectation.asRV s) := by
      -- `asRV s` is the state path `fun ω i => s i ω`.
      exact Measurable.of_eval hsm
    have hterm_eq : ∀ (σ : ℕ → 𝒮) t,
        Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
          (fun act =>
            (Â t (σ t) act •
                ∇[θ] ((M θ).condProb
                  (JointRandomSymbol (a.toFun t) (s.toFun t)) (act, σ t)).toReal) /
              ((M[σ t] θ').prob id act).toReal) =
        Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
          (fun u => (Â t (σ t) u • ∇[θ] (M.policy.prob θ (σ t) u)) /
            M.policy.prob θ' (σ t) u) := fun σ t => by
      have hnum :
          (fun act =>
            (Â t (σ t) act •
                ∇[θ] ((M θ).condProb
                  (JointRandomSymbol (a.toFun t) (s.toFun t)) (act, σ t)).toReal) /
              ((M[σ t] θ').prob id act).toReal) =
          (fun act =>
            (Â t (σ t) act • ∇[θ] (M.policy.prob θ (σ t) act)) /
              ((M[σ t] θ').prob id act).toReal) := by
        funext act
        have hgrad :
            ∇[θ] ((M θ).condProb
                (JointRandomSymbol (a.toFun t) (s.toFun t)) (act, σ t)).toReal =
              ∇[θ] (M.policy.prob θ (σ t) act) := by
          refine congrArg (gradient · θ) ?_
          funext κ
          simpa using hπeq κ t ⟨fun _ => σ t⟩ ⟨fun _ => act⟩
        rw [hgrad]
      have hden :
          (fun act => ((M[σ t] θ').prob id act).toReal)
            =ᵐ[(M[σ t] θ')] (M.policy.prob θ' (σ t)) := by
        have hrn :
            ((M[σ t] θ').map (id : 𝒜 → 𝒜)).rnDeriv ReferenceMeasure.measure
              =ᵐ[ReferenceMeasure.measure] M.policy.dens θ' (σ t) := by
          rw [Measure.map_id, hμ (σ t)]
          exact Measure.rnDeriv_withDensity _ (hdens (σ t))
        have hpt : (fun act => (M.policy.dens θ' (σ t) act).toReal) =
            M.policy.prob θ' (σ t) := by
          funext act
          simp [DensityPolicy.dens,
            ENNReal.toReal_ofReal (M.policy.nonneg θ' (σ t) act)]
        have hμs : M[σ t] θ' =
            ReferenceMeasure.measure.withDensity (M.policy.dens θ' (σ t)) :=
          hμ (σ t)
        have habs : (M[σ t] θ') ≪ ReferenceMeasure.measure := by
          rw [hμs]
          exact withDensity_absolutelyContinuous _ _
        have hto :
            (fun act => ((M[σ t] θ').prob id act).toReal)
              =ᵐ[ReferenceMeasure.measure]
              (fun act => (M.policy.dens θ' (σ t) act).toReal) := by
          simp only [Measure.prob]
          exact hrn.mono fun _ h => congrArg ENNReal.toReal h
        filter_upwards [habs.ae_le hto] with act hact
        exact hact.trans (congrFun hpt act)
      rw [hnum, Expectation.ofRV, Expectation.ofRV, expectation_bochner,
        expectation_bochner, Measure.map_id]
      refine integral_congr_ae ?_
      filter_upwards [hden] with act hact
      rw [hact]
    have hdot :
        (fun σ : ℕ → 𝒮 => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t =>
          Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
            (fun act =>
              (Â t (σ t) act •
                  ∇[θ] ((M θ).condProb
                    (JointRandomSymbol (a.toFun t) (s.toFun t)) (act, σ t)).toReal) /
                ((M[σ t] θ').prob id act).toReal)) =
        fun σ => ∑' t, γ ^ t • Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
          (fun u => (Â t (σ t) u • ∇[θ] (M.policy.prob θ (σ t) u)) /
            M.policy.prob θ' (σ t) u) := by
      funext σ
      simp only [hterm_eq σ]
      rfl
    rw [hdot]
    have hpath_t : ∀ t, s t = (fun σ : ℕ → 𝒮 => σ t) ∘ Expectation.asRV s := fun t => by
      funext ω
      rfl
    have htσ : ∀ t, ∀ᵐ σ ∂((M θ).map (Expectation.asRV s)),
        innerC t (σ t) =
          Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
            (fun u => (Â t (σ t) u • ∇[θ] (M.policy.prob θ (σ t) u)) /
              M.policy.prob θ' (σ t) u) := fun t => by
      have hcomp : Measure.map (s t) (M θ) =
          Measure.map (fun σ : ℕ → 𝒮 => σ t) ((M θ).map (Expectation.asRV s)) := by
        rw [Measure.map_map (measurable_pi_apply t) hpS]
        exact congrArg (fun f => Measure.map f (M θ)) (hpath_t t)
      have hclip := hinner_clip t
      rw [hcomp] at hclip
      exact ae_of_ae_map (measurable_pi_apply t).aemeasurable hclip
    have hae : ∀ᵐ σ ∂((M θ).map (Expectation.asRV s)),
        (∑' t, γ ^ t • innerC t (σ t)) =
          ∑' t, γ ^ t • Expectation.ofRV (M[σ t] θ') (id : 𝒜 → 𝒜)
            (fun u => (Â t (σ t) u • ∇[θ] (M.policy.prob θ (σ t) u)) /
              M.policy.prob θ' (σ t) u) := by
      filter_upwards [(ae_all_iff (ι := ℕ)).mpr htσ] with σ hσ
      exact tsum_congr fun t => by rw [hσ t]
    refine (integral_map hx (hinner_path.congr hae)).trans ?_
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    refine tsum_congr fun t => ?_
    rfl
  refine (congrArg (fun F : ℕ → (ℕ → 𝒮) → (ℕ → 𝒜) → (ℕ → ℝ) → ℝ =>
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        (F t (fun j => s j) (fun j => a j) (fun j => r j) •
          ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log))) hsrc).trans ?_
  refine hLHS.trans ?_
  refine (integral_congr_ae (Eventually.of_forall fun ω =>
    tsum_congr fun t => by rw [hscore_eq t ω])).trans ?_
  refine hswap_G.trans ?_
  have hterms :
      ∑' t, γ ^ t • ∫ ω, Gfun t ω •
          ∇[θ] Real.log (M.policy.prob θ (s t ω) (a t ω)) ∂(M θ) =
        ∑' t, γ ^ t • ∫ y, innerC t y ∂((M θ).map (s t)) :=
    tsum_congr fun t => by
      refine congrArg (fun z => γ ^ t • z) (htermC t)
  refine hterms.trans ?_
  refine hswap_C.trans ?_
  refine Eq.trans (integral_congr_ae ?_) hRHS.symm
  filter_upwards [hC_ae] with ω hω
  exact tsum_congr fun t => by rw [hω t]


-- created on 2026-11-11
-- updated on 2026-11-11

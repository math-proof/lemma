import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
import Lemma.Random.ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
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
action-integral bound of the continuous-action GAE, and `V_θ[t] δ k := M.Vkd θ γ (δ k)`.
- [GAE (discrete)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Icc.In_Ico)
- [GAE (continuous)](?module=Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (h₂ : ∀ t, (· t) = (r t, s t, a t))
  [htr : DensityModel.IsPolicyTrajectory M r s a]
  [haj : DensityModel.AbsContJointAS M a s]
  (hfactor : ∀ θ t x u,
    (M θ).prob (a t, s t) (u, x) =
      ENNReal.ofReal (M.policy.prob θ x u) *
        ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x)
  (hdens : ∀ θ t x,
    ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ 0 ∧
      ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ ⊤)
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₄ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₅ : ∀ x, ∑ u, g x u ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)))
  (hMs : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _ δ k => M.Vkd θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  have hμ : (ReferenceMeasure.measure : Measure A) = Measure.count :=
    CountableMeasure.measure_eq_count
  apply GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Icc.In_Ico
    (M := M) (Cg := Cg) h₀ h₁ htr haj
    (fun θ t sb ab =>
      (ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity.All_Eq_JointDens
        (M := M) htr haj (hfactor θ t (sb t) (ab t)) (hdens θ t (sb t)).1 (hdens θ t (sb t)).2).symm)
    hπ h₃ h₄
  ·
    intro x
    rw [hμ]
    apply integrable_count_iff.mpr Summable.of_finite
  ·
    intro x
    rw [hμ, integral_count]
    apply h₅
  ·
    apply hφ
  ·
    apply hMs


-- created on 2026-11-01
-- updated on 2026-11-02

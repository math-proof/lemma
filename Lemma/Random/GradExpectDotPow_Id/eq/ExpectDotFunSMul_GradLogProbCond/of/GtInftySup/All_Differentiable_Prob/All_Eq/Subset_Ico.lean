import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq.In_Icc.In_Ico
import sympy.core.function
import Lemma.Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure


/--
Generalized advantage estimation with the paper's weighted-average estimator (Schulman et al., arXiv 1506.02438, Eq. (16)):
with the temporal-difference residuals `δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` and `λ ∈ [0, 1)`, the
exponentially weighted average of the `(k + 1)`-step advantage estimates
`A[t] = (1 - λ) * ∑' k, λ ^ k * ∑ i ∈ range (k + 1), γ ^ i * δ[t + i]` gives
(`Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico`, the residuals being almost surely bounded since
`V` is the value function, `AeNormSub.le.DeltaBound.of.In_Ico`) and applies
`Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq.In_Icc.In_Ico`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ({γ, ℓ} : Set ℝ) ⊆ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ s a, Differentiable ℝ (M.policy.prob · s a))
  (h₃ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞)
  (hP0 : ∀ θ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0)
  (hπ : ∀ θ y u, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V : Θ ⇀ ℕ ⇀ (ℕ ⇀ S) → ℝ := ⟨fun θ => ⟨fun t («s.bvar» : ℕ ⇀ S) =>
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t] = «s.bvar»[t])⟩⟩
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun t δ k => V[θ, t + k] ⟨fun _ => δ k⟩⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ (γ ^ range (k + 1)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ V V_θ
  simp only [FinsetPow.dot_eq]
  classical
  have hγ : γ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ₀ : ℓ ∈ Set.Ico 0 1 := h₀ (by simp)
  have hℓ : ℓ ∈ Set.Icc 0 1 := ⟨hℓ₀.1, hℓ₀.2.le⟩
  -- unpack Fun; proof body keeps CoeFun/function style (same policy as V)
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₃o := h₃
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₃
  obtain ⟨C, hC⟩ := id h₃
  have h₇ : ∀ θ s a, ‖fderiv ℝ (fun θ => M.policy.prob θ s a) θ‖ ≤ C := fun θ s a => hC ⟨(θ, s, a), rfl⟩
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) →
      V θ' t ⟨fun _ => x⟩ = 𝔼[r : M θ']((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x) := fun θ' t x _ =>
    rfl
  -- almost surely the learned value is the time-free value function
  have hVc : ∀ᵐ ω ∂(M θ), ∀ k, V θ k ⟨fun _ => s k ω⟩ = M.Vc θ γ (s k ω) :=
    (AeRealPreimageSS.ne.Zero (s := s) (M := M) θ).mono fun ω h k =>
      (hVr θ k _ (h k)).trans <| by
        change M.V θ γ k (s k ω) = M.Vc θ γ (s k ω)
        exact Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ k (s k ω) hγ
          (by simpa [s] using h k) (hP0 θ (s k ω))
  have hδ : ∀ᵐ ω ∂(M θ), ∀ j, r j ω + γ * V θ (j + 1) ⟨fun _ => s (j + 1) ω⟩ - V θ j ⟨fun _ => s j ω⟩ =
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  -- almost surely the residuals are bounded
  have hbdd : ∀ᵐ ω ∂(M θ),
      BddAbove (Set.range fun j => |r j ω + γ * V θ (j + 1) ⟨fun _ => s (j + 1) ω⟩ - V θ j ⟨fun _ => s j ω⟩|) := by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico (M := M) hγ h₁ θ, hδ] with ω h1 h2
    refine ⟨(3 / (1 - γ) - 1) * |M.env.R|, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := h1 j
    rw [Real.norm_eq_abs] at this
    beta_reduce
    rwa [h2 j]
  -- almost surely the paper's estimator is the closed form
  have hpt : ∀ᵐ ω ∂(M θ), ∀ t,
      (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V θ (t + i + 1) ⟨fun _ => s (t + i + 1) ω⟩ - V θ (t + i) ⟨fun _ => s (t + i) ω⟩)) =
      ((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (fun k : ℕ => r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩) := by
    filter_upwards [hbdd] with ω hb t
    exact Real.MulSub1_Dot_FunDotPow_Range.eq.DotPow_Id.of.GtInftySup.Subset_Ico
      (δ := ⟨fun j => r j ω + γ * V θ (j + 1) ⟨fun _ => s (j + 1) ω⟩ - V θ j ⟨fun _ => s j ω⟩⟩) (t := t) h₀ hb
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
      r k ω + γ * V θ (k + 1) ⟨fun _ => s (k + 1) ω⟩ - V θ k ⟨fun _ => s k ω⟩ := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ k).add (((measurable_of_countable (fun x : S => V θ (k + 1) ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (fun x : S => V θ k ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ k))
  -- the expectation of a pathwise functional is a Bochner integral
  have hexp : ∀ F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ,
      (∀ t, Measurable fun ω : ℕ → ℝ × S × A => F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω)) →
      𝔼[r, s, a : M θ](
        (γ ^ (id : ℕ → ℕ)) @ fun t ↦ (F t s a r •
          ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) =
      ∫ ω, ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
        ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
    intro F hF
    have hg := fun t : ℕ =>
      StronglyMeasurable.smul (hF t).stronglyMeasurable
        ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
          gradient (fun θ' => (ℙ[M θ']((a t) = p.2 | (s t) = p.1) : ℝ).log) θ)).comp_measurable
            ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))
    have hGsm : StronglyMeasurable fun ω : ℕ → ℝ × S × A =>
        ∑' t, γ ^ t • (F t (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) •
          ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) :=
      StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
        (hg t).const_smul (γ ^ t)
    let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
      fun t => (p.1 t, p.2.1 t, p.2.2 t)
    have fromPath_meas : Measurable fromPath :=
      Measurable.of_eval fun t =>
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    ·
      exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath]
          rfl)
    simp only [AsPathRV.path_process, JointRandomSymbol]
    rfl
  have hF₁ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
      (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V θ (t + i + 1) ⟨fun _ => s (t + i + 1) ω⟩ - V θ (t + i) ⟨fun _ => s (t + i) ω⟩)) := fun t => by
    show Measurable fun ω : ℕ → ℝ × S × A =>
      (1 - ℓ) * ∑' k, ℓ ^ k * ∑ i ∈ range (k + 1), γ ^ i *
        (r (t + i) ω + γ * V θ (t + i + 1) ⟨fun _ => s (t + i + 1) ω⟩ - V θ (t + i) ⟨fun _ => s (t + i) ω⟩)
    exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
      (Finset.measurable_sum _ fun i _ => (hmeas (t + i)).const_mul _).const_mul _).const_mul _
  have hF₂ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
      (((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (fun k : ℕ => r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)) := fun t => by
    show Measurable fun ω : ℕ → ℝ × S × A => ∑' k, (γ * ℓ) ^ k *
      (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)
    exact Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k => (hmeas (t + k)).const_mul _
  -- relate statement V_θ to paper V
  have eqVθ : ∀ t (δ : ℕ → S) k, V_θ[t] δ k = V θ (t + k) ⟨fun _ => δ k⟩ := by
    intro t δ k
    simp [V_θ]
  have hδθ : ∀ (s : ℕ → S) (r : ℕ → ℝ) (t : ℕ),
      (fun k => r (t + k) + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1)⟩ - V θ (t + k) ⟨fun _ => s (t + k)⟩) =
        r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:] := by
    intro s r t
    funext k
    have hk : t + k + 1 = t + 1 + k := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, eqVθ t s[t:] k, eqVθ (t + 1) s[t + 1:] k]
    simp only [Function.getSliceFrom_apply]
  have hFθ : ∀ t, Measurable fun ω : ℕ → ℝ × S × A =>
      (((γ * ℓ) ^ (id : ℕ → ℕ)) @
        ((fun j => r j ω)[t:] + γ • V_θ[t + 1] (fun j => s j ω)[t + 1:] -
          V_θ[t] (fun j => s j ω)[t:])) := fun t => by
    convert hF₂ t using 1
    funext ω
    exact congrArg (fun δ => Dot.dot ((γ * ℓ) ^ (id : ℕ → ℕ)) δ)
      (hδθ (fun j => s j ω) (fun j => r j ω) t).symm
  refine (GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq.In_Icc.In_Ico
    (θ := θ) hγ hℓ h₁ h₂ h₃o hP0 hπ).trans ?_
  symm
  -- V_θ[t] s[t:] i = V θ (t + i) ⟨fun _ => s (t + i)⟩
  have hres : ∀ (s : ℕ → S) (t i : ℕ),
      V_θ[t] s[t:] i = V θ (t + i) ⟨fun _ => s (t + i)⟩ ∧
      V_θ[t + 1] s[t + 1:] i = V θ (t + i + 1) ⟨fun _ => s (t + i + 1)⟩ := by
    intro s t i
    refine ⟨?_, ?_⟩
    · simpa [Function.getSliceFrom_apply] using eqVθ t s[t:] i
    ·
      have hk : t + 1 + i = t + i + 1 := by omega
      simpa [Function.getSliceFrom_apply, hk] using eqVθ (t + 1) s[t + 1:] i
  -- F_θ (imply) = F_raw pointwise, so their path expectations agree
  have hFeq :
    (fun t (s : ℕ → S) (a : ℕ → A) (r : ℕ → ℝ) =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]) i)) =
      (fun t s a r =>
        (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
          (r (t + i) + γ * V θ (t + i + 1) ⟨fun _ => s (t + i + 1)⟩ - V θ (t + i) ⟨fun _ => s (t + i)⟩))) := by
    funext t s a r
    congr 1
    congr 1
    funext k
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.getSliceFrom_apply]
    rw [(hres s t i).1, (hres s t i).2]
  refine (congrArg
      (fun F : ℕ → (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℝ =>
        𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          (F t (fun j => s j) (fun j => a j) (fun j => r j) •
            ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)))
      hFeq).trans ?_
  refine (hexp (fun t s a r => (1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) @ fun k ↦ ∑ i ∈ range (k + 1), γ ^ i *
      (r (t + i) + γ * V θ (t + i + 1) ⟨fun _ => s (t + i + 1)⟩ - V θ (t + i) ⟨fun _ => s (t + i)⟩))) hF₁).trans
    ((integral_congr_ae ?_).trans
      (hexp (fun t s a r => ((γ * ℓ) ^ (id : ℕ → ℕ)) @
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) hFθ).symm)
  filter_upwards [hpt] with ω h
  refine tsum_congr fun t => ?_
  rw [h t, hδθ (fun j => s j ω) (fun j => r j ω) t]


-- created on 2026-10-19

import Lemma.Random.Eq_Expect_FunPowDot.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondTSum_MulPow.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico
import sympy.core.function
open MeasureTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure
open scoped ENNReal.ToRealCoe


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : Fun ℕ ((ℕ → ℝ × S × A) → ℝ)}
  {s : Fun ℕ ((ℕ → ℝ × S × A) → S)}
  {a : Fun ℕ ((ℕ → ℝ × S × A) → A)}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (h₂ : ∀ t, (· t) = (r t, s t, a t))
  (h₃ : ∀ s a, Differentiable ℝ (M.policy.prob · s a))
  (h₄ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace_Path.of.All_PSpace hs
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace_Path.of.All_PSpace ha
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V : Fun Θ (Fun ℕ (Fun ℕ S → ℝ)) := ⟨fun θ => ⟨fun t («s.bvar» : Fun ℕ S) =>
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t] = «s.bvar»[t])⟩⟩
  let V_θ : Fun ℕ ((ℕ → S) → ℕ → ℝ) := ⟨fun t δ k => V[θ, t + k] ⟨fun _ => δ k⟩⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _ _ _ _ V V_θ
  classical
  -- unpack Fun; proof body keeps CoeFun/function style (same policy as V)
  rcases r with ⟨r⟩
  rcases s with ⟨s⟩
  rcases a with ⟨a⟩
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₂ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₂ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₂ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₁.1, (mul_le_of_le_one_right h₀.1 h₁.2).trans_lt h₀.2⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₂ h₃ h₄ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₂ CountableMeasure.measure_eq_count CountableMeasure.measure_eq_count (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₂)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) →
      V θ' t ⟨fun _ => x⟩ = 𝔼[r : M θ']((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x) := fun θ' t x _ =>
    rfl
  -- almost surely the learned value is the time-free value function
  have hVc : ∀ᵐ ω ∂(M θ), ∀ k, V θ k ⟨fun _ => s k ω⟩ = M.Vc θ γ (s k ω) :=
    (AeRealPreimageSS.ne.Zero (s := s) (M := M) θ).mono fun ω h k =>
      (hVr θ k _ (h k)).trans (Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ k _ h₀ h₂ (h k))
  have hδ : ∀ᵐ ω ∂(M θ), ∀ j, r j ω + γ * V θ (j + 1) ⟨fun _ => s (j + 1) ω⟩ - V θ j ⟨fun _ => s j ω⟩ =
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  have hbd : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)‖ ≤
        (1 - c)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|) := by
    intro c hc'
    filter_upwards [AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico (M := M) h₀ h₂ hc' θ, hδ] with ω h1 h2 t
    have e : ∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩) =
        ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω)) :=
      tsum_congr fun k => by rw [h2 (t + k)]
    exact e.symm ▸ h1 t
  -- the `c`-discounted advantage against the score only sees the first residual
  have hinner : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ t, ∫ ω,
      (∑' k, c ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    intro c hc' t
    refine (integral_congr_ae ?_).trans
      (Integral_SMul.of.In_Ico.In_Ico (M := M) h₀ h₂ θ hc' t (fun y u => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ))
    filter_upwards [hscore t, hδ] with ω h1 h2
    rw [h1]
    congr 1
    exact tsum_congr fun k => by rw [h2 (t + k)]
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
      (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) =>
          r k + γ * V θ (k + 1) ⟨fun _ => s (k + 1)⟩ - V θ k ⟨fun _ => s k⟩)
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₂ k).add
      (((measurable_of_countable (fun x : S => V θ (k + 1) ⟨fun _ => x⟩)).comp
          (Random.Measurable.of.All_Eq.snd.fst h₂ (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (fun x : S => V θ k ⟨fun _ => x⟩)).comp
        (Random.Measurable.of.All_Eq.snd.fst h₂ k))
  have hbase : ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k) + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1)⟩ - V θ (t + k) ⟨fun _ => s (t + k)⟩)) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) :=
    have h₂old : ∀ θ t x, ((M θ) (s t ⁻¹' {x}) ≠ 0) →
        V θ t ⟨fun _ => x⟩ = 𝔼[r : M θ](∑' k, γ ^ k * r (t + k) | s t = x) := fun θ t x _ =>
      rfl
    Eq_Expect_FunPowDot.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondTSum_MulPow.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
      h₀ h₂ CountableMeasure.measure_eq_count CountableMeasure.measure_eq_count h₂old h₃ h₄
  have hA₁ := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
    (X := fun s _ r k => r k + γ * V θ (k + 1) ⟨fun _ => s (k + 1)⟩ - V θ k ⟨fun _ => s k⟩) (c := γ)
    h₀ h₂ CountableMeasure.measure_eq_count CountableMeasure.measure_eq_count hmeas (hbd γ h₀) h₃ h₄
  have hA₂ := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
    (X := fun s _ r k => r k + γ * V θ (k + 1) ⟨fun _ => s (k + 1)⟩ - V θ k ⟨fun _ => s k⟩) (c := γ * ℓ)
    h₀ h₂ CountableMeasure.measure_eq_count CountableMeasure.measure_eq_count hmeas (hbd (γ * ℓ) hc) h₃ h₄
  -- hsplit lands on left-assoc r[t:] + A - B (same shape as flatter imply)
  have hsplit :
      ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
        𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + (fun k => γ * V[θ][t:] (k + 1) ⟨fun _ => s[t:] (k + 1)⟩) - (fun k => V[θ][t:] k ⟨fun _ => s[t:] k⟩))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) :=
    hbase.trans (hA₁.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm (tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t])).trans hA₂))
  refine hsplit.trans ?_
  change
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + (fun k => γ * V[θ][t:] (k + 1) ⟨fun _ => s[t:] (k + 1)⟩) - (fun k => V[θ][t:] k ⟨fun _ => s[t:] k⟩))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)
  refine congrArg
    (Expectation.ofRV (M θ)
      (JointRandomSymbol (Expectation.asRV r)
        (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a)))) ?_
  funext integ
  dsimp
  congr 1
  funext t
  congr 1
  congr 1
  -- flatter imply is left-assoc like hsplit; peel Sub (B defeq via let V_θ), then Add; match A via new time-first V_θ
  congr 1
  · -- r[t:] + A = r[t:] + (γ • V_θ[t + 1] s[t + 1:])
    congr 1
    dsimp only [V_θ]
    funext k
    have hk : t + (k + 1) = (t + 1) + k := by omega
    simp only [Function.getSliceFrom_apply, hk, Pi.smul_apply, smul_eq_mul, Fun.getElem_eq]


-- created on 2026-10-01
-- updated on 2026-10-19

import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Ico
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico
import Theorem.Dynamics.PolicyTrajectory
open MeasureTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory
set_option linter.style.haveILetI false


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
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  [h₂ : IsPolicyTrajectory M r s a]
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t))
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.Measurable (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _ _ _ V_θ
  have : IsPolicyTrajectory M r s a := h₂
  classical
  have : IsProbabilityMeasure M.env.init := M.env.init_prob
  have : Nonempty S := nonempty_of_isProbabilityMeasure M.env.init
  have : Nonempty A := by
    have hsum := M.policy.sum_eq_one (0 : Θ) (Classical.arbitrary S)
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  -- unpack Fun; proof body keeps CoeFun/function style (same policy as V)
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₂.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₂.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₂.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have hDiffPol : ∀ x u, Differentiable ℝ (M.policy.prob · x u) := h₃
  have hSupPol : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞ := h₄
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₁.1, (mul_le_of_le_one_right h₀.1 h₁.2).trans_lt h₀.2⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₂.stage_eq hDiffPol hSupPol t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₂.stage_eq (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₂.stage_eq)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  -- V = V0 definitionally (time-homogeneous series)
  have hVc : ∀ᵐ ω ∂(M θ), ∀ k, M.V θ γ k (s k ω) = M.V0 θ γ (s k ω) :=
    Filter.Eventually.of_forall fun _ _ => rfl
  have hδ : ∀ᵐ ω ∂(M θ), ∀ j, r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω) =
      r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  have hbd : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))‖ ≤
        (1 - c)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|) := by
    intro c hc'
    filter_upwards [AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico (M := M) h₀ h₂.stage_eq hc' θ, hδ] with ω h1 h2 t
    exact (tsum_congr fun k => by rw [h2 (t + k)] : ∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω)) =
        ∑' k, c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) - M.V0 θ γ (s (t + k) ω))).symm ▸ h1 t
  -- the `c`-discounted advantage against the score only sees the first residual
  have hinner : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ t, ∫ ω,
      (∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∫ ω, (r t ω + γ * M.V0 θ γ (s (t + 1) ω) - M.V0 θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    intro c hc' t
    let ψ : S → A → (Θ →L[ℝ] ℝ) := fun y u =>
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
    trans ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) -
        M.V0 θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ)
    ·
      refine integral_congr_ae ?_
      filter_upwards [hscore t] with ω h1
      simp [h1, ψ, Model.V]
    ·
      have hE := Integral_SMul.of.In_Ico.In_Ico (M := M) h₀ h₂.stage_eq hc' θ t ψ
      let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
        fun n => (p.1 n, p.2.1 n, p.2.2 n)
      have fromPath_meas : Measurable fromPath :=
        Measurable.of_eval fun n =>
          ((measurable_pi_apply n).comp measurable_fst).prodMk
            (((measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)).prodMk
              ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)))
      have hδj : ∀ j, Measurable fun ω : ℕ → ℝ × S × A =>
          r j ω + γ * M.V0 θ γ (s (j + 1) ω) - M.V0 θ γ (s j ω) := fun j =>
        ((Random.Measurable.of.All_Eq.fst h₂.stage_eq j).add
          (((measurable_of_countable (M.V0 θ γ)).comp
              (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq (j + 1))).const_mul γ)).sub
          ((measurable_of_countable (M.V0 θ γ)).comp (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq j))
      have hψω : StronglyMeasurable fun ω : ℕ → ℝ × S × A => ψ (s t ω) (a t ω) :=
        (StronglyMeasurable.of_discrete (f := fun p : S × A => ψ p.1 p.2)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₂.stage_eq t))
      let δL : (ℕ → ℝ × S × A) → ℝ := fun ω =>
        ∑' k, c ^ k * (r (t + k) ω + γ * M.V0 θ γ (s (t + k + 1) ω) - M.V0 θ γ (s (t + k) ω))
      let ψt : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := fun ω => ψ (s t ω) (a t ω)
      let Gleft : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := δL • ψt
      have hGleft : StronglyMeasurable Gleft := by
        convert ((Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
          (hδj (t + k)).const_mul (c ^ k)).stronglyMeasurable).smul hψω
      let δR : (ℕ → ℝ × S × A) → ℝ := fun ω =>
        r t ω + γ * M.V0 θ γ (s (t + 1) ω) - M.V0 θ γ (s t ω)
      let Gright : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := δR • ψt
      have hGright : StronglyMeasurable Gright := by
        convert (hδj t).stronglyMeasurable.smul hψω
      have hL :
        𝔼[r, s, a : M θ]((∑' k, c ^ k * (r (t + k) + γ * M.V0 θ γ (s (t + k + 1)) -
            M.V0 θ γ (s (t + k)))) • ψ (s t) (a t)) =
          ∫ ω, Gleft ω ∂(M θ) := by
        have : PSpace (M θ) (AsPathRV.path s) :=
          PSpace_Path.of.All_PSpace
            (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq j).aemeasurable⟩)
        have : PSpace (M θ) (AsPathRV.path a) :=
          PSpace_Path.of.All_PSpace
            (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₂.stage_eq j).aemeasurable⟩)
        have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
          PSpace_Path.of.All_PSpace
            (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₂.stage_eq j).aemeasurable⟩)
        have hx : AEMeasurable
          (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
          PSpace.aemeasurable
        simp only [AsPathRV.path_process]
        rw [Expectation.ofRV, expectation_bochner]
        refine (integral_map hx ?_).trans ?_
        ·
          exact (hGleft.comp_measurable fromPath_meas).aestronglyMeasurable.congr
            (Filter.Eventually.of_forall fun p => by
              simp only [Function.comp_apply, fromPath, Gleft, δL, ψt]
              rfl)
        ·
          simp only [AsPathRV.path_process, JointRandomSymbol, Gleft, δL, ψt]
          rfl
      refine hL.symm.trans (hE.trans ?_)
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₂.stage_eq j).aemeasurable⟩)
      have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₂.stage_eq j).aemeasurable⟩)
      have hx : AEMeasurable
        (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
        PSpace.aemeasurable
      rw [Expectation.ofRV, expectation_bochner]
      refine (integral_map hx ?_).trans ?_
      ·
        exact (hGright.comp_measurable fromPath_meas).aestronglyMeasurable.congr
          (Filter.Eventually.of_forall fun p => by
            simp only [Function.comp_apply, fromPath, Gright, δR, ψt]
            rfl)
      ·
        simp only [AsPathRV.path_process, JointRandomSymbol]
        rfl
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
      (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) =>
          r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k))
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₂.stage_eq k).add
      (((measurable_of_countable (fun x : S => M.V θ γ (k + 1) x)).comp
          (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (fun x : S => M.V θ γ k x)).comp
        (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq k))
  have hbase : ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
          ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) :=
    GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Ico.advantage
      h₀ (h₁ := h₂) h₃ h₄
  have hbaseexp : ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k) + γ * M.V θ γ (t + k + 1) (s (t + k + 1)) - M.V θ γ (t + k) (s (t + k)))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
    refine hbase.trans ?_
    refine congrArg
      (Expectation.ofRV (M θ)
        ((Expectation.asRV r, Expectation.asRV s, Expectation.asRV a))) ?_
    funext integ
    dsimp
    congr 1
    funext t
    congr 1
    congr 1
    dsimp only [V_θ]
    funext k
    have hk : t + 1 + k = t + k + 1 := by omega
    simp only [Function.getSliceFrom_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hk]
  have hA₁ := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
    (X := fun s _ r k => r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k)) (c := γ)
    h₀ h₂.stage_eq hmeas (hbd γ h₀) hDiffPol hSupPol
  have hA₂ := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
    (X := fun s _ r k => r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k)) (c := γ * ℓ)
    h₀ h₂.stage_eq hmeas (hbd (γ * ℓ) hc) hDiffPol hSupPol
  -- hsplit lands on left-assoc r[t:] + A - B (same shape as flatter imply)
  have hsplit :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + (fun k => γ * M.V θ γ (t + (k + 1)) (s[t:] (k + 1))) - (fun k => M.V θ γ (t + k) (s[t:] k)))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) :=
    hbaseexp.trans (hA₁.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm (tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t])).trans hA₂))
  refine hsplit.trans ?_
  change
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + (fun k => γ * M.V θ γ (t + (k + 1)) (s[t:] (k + 1))) - (fun k => M.V θ γ (t + k) (s[t:] k)))) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ (((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)
  refine congrArg
    (Expectation.ofRV (M θ)
      ((Expectation.asRV r, Expectation.asRV s, Expectation.asRV a))) ?_
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
    simp only [Function.getSliceFrom_apply, hk, Pi.smul_apply, smul_eq_mul]


-- created on 2026-10-01
-- updated on 2026-11-02

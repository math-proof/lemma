import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_NeProb_0.IsPolicyTrajectory.In_Ico
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico1
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico
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
  (h₂ : IsPolicyTrajectory M r s a)
  (h₃ : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) ≠ 0)
  (h₄ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₅ : sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t)
      CountableMeasure.measure_eq_count
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₂.stage_eq t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
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
  -- joint ℙ(a[0]∧s[0]) = ℙ(s[0]) * ℙ(a[0]|s[0]) (counting); recover product form of joint h₃
  have hπ_mul : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
      (ℙ[M θ](s[0] = «s.bvar»[0])) * (ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0])) ≠ 0 := by
    intro θ «s.bvar» «a.bvar»
    have hj := h₃ θ «s.bvar» «a.bvar»
    have hαβ : (ReferenceMeasure.measure : Measure (A × S)) = Measure.count := by
      change (ReferenceMeasure.measure : Measure A).prod ReferenceMeasure.measure = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS]
    have hJ : ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) =
        (M θ) ((a 0) ⁻¹' {«a.bvar»[0]} ∩ (s 0) ⁻¹' {«s.bvar»[0]}) := by
      rw [Prob.eq.Measure.of.Eq_Count («π» := M θ) (x := (a 0, s 0)) hαβ]
      congr 1
      ext ω
      simp [JointRandomSymbol, Prod.ext_iff]
    have hS : ℙ[M θ](s[0] = «s.bvar»[0]) = (M θ) ((s 0) ⁻¹' {«s.bvar»[0]}) :=
      Prob.eq.Measure.of.Eq_Count («π» := M θ) (x := s 0) CountableMeasure.measure_eq_count «s.bvar»[0]
    have hD : ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0]) =
        (M θ) ((a 0) ⁻¹' {«a.bvar»[0]} ∩ (s 0) ⁻¹' {«s.bvar»[0]}) /
          (M θ) ((s 0) ⁻¹' {«s.bvar»[0]}) :=
      ProbCond.eq.Div.of.SinglePSpace inferInstance («π» := M θ) (x := a 0) (y := s 0)
        «a.bvar»[0] «s.bvar»[0]
    have hs0 : (M θ) ((s 0) ⁻¹' {«s.bvar»[0]}) ≠ 0 := by
      have hne : (M θ) ((a 0) ⁻¹' {«a.bvar»[0]} ∩ (s 0) ⁻¹' {«s.bvar»[0]}) ≠ 0 := by
        rwa [← hJ]
      intro h0
      exact hne <| nonpos_iff_eq_zero.mp <|
        (measure_mono Set.inter_subset_right).trans_eq h0
    have heq : ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) =
        (ℙ[M θ](s[0] = «s.bvar»[0])) * (ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0])) := by
      rw [hJ, hS, hD]
      exact (ENNReal.mul_div_cancel hs0 (measure_ne_top (M θ) _)).symm
    rwa [← heq]
  -- hP0 follows from product form: pick any constant action path; left ENNReal factor ≠ 0
  have hP0 : ∀ θ («s.bvar» : ℕ ⇀ S), ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 := by
    intro θ «s.bvar»
    have ⟨hs0, _⟩ : ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 ∧
        ℙ[M θ](a[0] = (⟨fun _ => Classical.arbitrary A⟩ : ℕ ⇀ A)[0] | s[0] = «s.bvar»[0]) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ «s.bvar» ⟨fun _ => Classical.arbitrary A⟩)
      rwa [not_or] at h
    exact hs0
  -- bridge P(s[0]) to .real before unpack (Fun CoeFun)
  have hP0raw : ∀ θ x, (M θ).real ((s 0) ⁻¹' {x}) ≠ 0 := by
    intro θ x
    have heqR : (ℙ[M θ](s[0] = x) : ℝ) = (M θ).real ((s 0) ⁻¹' {x}) := by
      rw [Prob.eq.Measure.of.Eq_Count («π» := M θ) (x := s 0) CountableMeasure.measure_eq_count x]
      rfl
    have heqE : ℙ[M θ](s[0] = x) = (M θ) ((s 0) ⁻¹' {x}) :=
      Prob.eq.Measure.of.Eq_Count («π» := M θ) (x := s 0) CountableMeasure.measure_eq_count x
    -- derived hP0 over constant path «s.bvar» = fun _ ↦ x; bare ENNReal ≠ 0 → ℝ via toReal
    rw [← heqR]
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨hP0 θ ⟨fun _ => x⟩, heqE ▸ measure_ne_top (M θ) _⟩
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
  -- bridge conditional-ℙ hyps to policy.prob facts expected by In_Icc.In_Ico
  have h_pol_eq : ∀ θ' x u, (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) = M.policy.prob θ' x u := by
    intro θ' x u
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₂.stage_eq (hP θ' 0) (hP0raw θ' x),
      ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]
  have hDiffPol : ∀ x u, Differentiable ℝ (M.policy.prob · x u) := by
    intro x u
    -- h₄ over constant paths fun _ ↦ x / fun _ ↦ u
    exact (funext fun θ' => (h_pol_eq θ' x u).symm) ▸ h₄ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
  have hSupPol : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞ := by
    obtain ⟨C, hC⟩ := h₅
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨θ', x, u⟩, rfl⟩
    have hgrad : ∇[θ'] M.policy.prob θ' x u =
        ∇[θ'] (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) := by
      refine Filter.EventuallyEq.gradient_eq ?_
      exact Filter.Eventually.of_forall fun θ'' => (h_pol_eq θ'' x u).symm
    change ‖∇[θ'] M.policy.prob θ' x u‖ ≤ C
    rw [hgrad]
    apply hC
    exact ⟨(θ', (0 : ℕ), (⟨fun _ => x⟩ : ℕ ⇀ S), (⟨fun _ => u⟩ : ℕ ⇀ A)), rfl⟩
  have hπraw : ∀ θ' y u, (M θ').real ((s 0) ⁻¹' {y}) * M.policy.prob θ' y u ≠ 0 := by
    intro θ' y u
    -- h₃ is ENNReal.mul ≠ 0 over constant paths; split and bridge each factor to ℝ
    have ⟨hs0, hcond⟩ : ℙ[M θ']((s 0) = y) ≠ 0 ∧
        ℙ[M θ']((a 0) = u | (s 0) = y) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ' ⟨fun _ => y⟩ ⟨fun _ => u⟩)
      rwa [not_or] at h
    have heqE : ℙ[M θ']((s 0) = y) = (M θ') ((s 0) ⁻¹' {y}) :=
      Prob.eq.Measure.of.Eq_Count («π» := M θ') (x := s 0) CountableMeasure.measure_eq_count y
    have hreal : (M θ').real ((s 0) ⁻¹' {y}) ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨heqE ▸ hs0, measure_ne_top (M θ') _⟩
    refine mul_ne_zero hreal ?_
    rw [← h_pol_eq θ' y u]
    refine ENNReal.toReal_ne_zero.mpr ⟨hcond, ?_⟩
    have hOF : ℙ[M θ']((a 0) = u | (s 0) = y) = ENNReal.ofReal (M.policy.prob θ' y u) :=
      ProbCond.eq.OfRealPol.of.Ne_0 h₂.stage_eq (hP θ' 0) (hP0raw θ' y)
    rw [hOF]
    apply ENNReal.ofReal_ne_top
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
  -- almost surely the learned value is the time-free value function
  have hVc : ∀ᵐ ω ∂(M θ), ∀ k, M.V θ γ k (s k ω) = M.Vc θ γ (s k ω) :=
    (AeRealPreimageSS.ne.Zero (s := s) (M := M) θ).mono fun ω h k =>
      V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ k (s k ω) h₀
        (by simpa [s] using h k) (hP0raw θ (s k ω))
  have hδ : ∀ᵐ ω ∂(M θ), ∀ j, r j ω + γ * M.V θ γ (j + 1) (s (j + 1) ω) - M.V θ γ j (s j ω) =
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) :=
    hVc.mono fun ω h j => by rw [h j, h (j + 1)]
  have hbd : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))‖ ≤
        (1 - c)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|) := by
    intro c hc'
    filter_upwards [AeAll_LeNorm_TSum_MulPowSubAddRMul_VcVcMulSub1DeltaBound.of.In_Ico.In_Ico (M := M) h₀ h₂.stage_eq hc' θ, hδ] with ω h1 h2 t
    exact (tsum_congr fun k => by rw [h2 (t + k)] : ∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω)) =
        ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))).symm ▸ h1 t
  -- the `c`-discounted advantage against the score only sees the first residual
  have hinner : ∀ c ∈ Set.Ico (0:ℝ) 1, ∀ t, ∫ ω,
      (∑' k, c ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    intro c hc' t
    let ψ : S → A → (Θ →L[ℝ] ℝ) := fun y u =>
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
    trans ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ)
    ·
      refine integral_congr_ae ?_
      filter_upwards [hscore t, hδ] with ω h1 h2
      rw [h1]
      congr 1
      exact tsum_congr fun k => by rw [h2 (t + k)]
    ·
      have hE := Integral_SMul.of.In_Ico.In_Ico (M := M) h₀ h₂.stage_eq hc' θ t ψ (hP0raw θ)
      let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
        fun n => (p.1 n, p.2.1 n, p.2.2 n)
      have fromPath_meas : Measurable fromPath :=
        Measurable.of_eval fun n =>
          ((measurable_pi_apply n).comp measurable_fst).prodMk
            (((measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)).prodMk
              ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)))
      have hδj : ∀ j, Measurable fun ω : ℕ → ℝ × S × A =>
          r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) := fun j =>
        ((Random.Measurable.of.All_Eq.fst h₂.stage_eq j).add
          (((measurable_of_countable (M.Vc θ γ)).comp
              (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq (j + 1))).const_mul γ)).sub
          ((measurable_of_countable (M.Vc θ γ)).comp (Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq j))
      have hψω : StronglyMeasurable fun ω : ℕ → ℝ × S × A => ψ (s t ω) (a t ω) :=
        (StronglyMeasurable.of_discrete (f := fun p : S × A => ψ p.1 p.2)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₂.stage_eq t).prodMk
            (Random.Measurable.of.All_Eq.snd.snd h₂.stage_eq t))
      let δL : (ℕ → ℝ × S × A) → ℝ := fun ω =>
        ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))
      let ψt : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := fun ω => ψ (s t ω) (a t ω)
      let Gleft : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := δL • ψt
      have hGleft : StronglyMeasurable Gleft := by
        convert ((Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
          (hδj (t + k)).const_mul (c ^ k)).stronglyMeasurable).smul hψω
      let δR : (ℕ → ℝ × S × A) → ℝ := fun ω =>
        r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)
      let Gright : (ℕ → ℝ × S × A) → (Θ →L[ℝ] ℝ) := δR • ψt
      have hGright : StronglyMeasurable Gright := by
        convert (hδj t).stronglyMeasurable.smul hψω
      have hL :
        𝔼[r, s, a : M θ]((∑' k, c ^ k * (r (t + k) + γ * M.Vc θ γ (s (t + k + 1)) -
            M.Vc θ γ (s (t + k)))) • ψ (s t) (a t)) =
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
      h₀ h₂ h₃ h₄ h₅
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
-- updated on 2026-10-21

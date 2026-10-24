import Lemma.Random.ExpectSMul.eq.ExpectSMulExpectCond.of.All_Eq.In_Ico
import Lemma.Random.ExpectDot.eq.Integral_Dot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
import Lemma.Random.GradExpectDotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Random.Integrable_Fun
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob
import Lemma.Random.Integrable.of.In_Ico
import Lemma.Random.V.eq.Integral.of.Measurable
import Lemma.Random.ExpectSum_SMulMulPow.eq.Integral_Sum_SMul_GradLogProbCond.of.IsPolicyTrajectory
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure Set
open IsPolicyTrajectory
set_option maxHeartbeats 625000
set_option linter.style.haveILetI false


/-- Path-binder V-gradient Expect = observation integral. -/
private lemma expect_gradV_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {n : ℕ}
  {V : Θ → S → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  [PSpace (M θ) (AsPathRV.path s)] :
  𝔼[s : M θ](∇[θ] (V θ (s n))) =
    ∫ ω, ∇[θ] (V θ (s n ω)) ∂(M θ) := by
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s) (M θ) := PSpace.aemeasurable
  refine (integral_map hx ?_).trans ?_
  ·
    exact (StronglyMeasurable.comp_measurable
      (f := fun x : S ↦ ∇[θ] (V θ x))
      StronglyMeasurable.of_discrete
      (measurable_pi_apply n)).aestronglyMeasurable
  ·
    simp only [AsPathRV.path_process]

/-- Ae equality: binder-equality ℙ-log-grad vs `M.policy.prob` log-grad. -/
private lemma gradLogProbCond_ae_eq_gradLogPol
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₄ : ∀ s a, Differentiable ℝ (M.policy.prob · s a))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP : ∀ θ t, SinglePSpace (M θ) (a t, s t)) :
  ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
  classical
  intro t
  filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₄ h₅ t (s t ω) θ).continuousAt
  have hfd :
    fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [gradient]
  exact congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd

/-- Path-binder finset Expect of an arbitrary score = observation integral (ℙ-free). -/
private lemma expect_finset_smul_score_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : ℕ → S → A → ℝ}
  {score : ℕ → S → A → Θ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  [PSpace (M θ) (AsPathRV.path s)]
  [PSpace (M θ) (AsPathRV.path a)] :
  𝔼[s, a : M θ](∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t) (a t)) • score t (s t) (a t)) =
    ∫ ω, ∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t ω) (a t ω)) • score t (s t ω) (a t ω) ∂(M θ) := by
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx ?_).trans ?_
  ·
    refine (Finset.stronglyMeasurable_fun_sum (Finset.range n) fun t _ => ?_).aestronglyMeasurable
    exact StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦ (γ ^ t * Q t q.1 q.2) • score t q.1 q.2)
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  ·
    simp only [JointRandomSymbol, AsPathRV.path_process]

/-- Ae pointwise score equality lifts to finset-smul observation integrals. -/
private lemma integral_finset_smul_score_eq_of_ae
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : ℕ → S → A → ℝ}
  {score₁ score₂ : ℕ → S → A → Θ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (hscore : ∀ t, ∀ᵐ ω ∂(M θ), score₁ t (s t ω) (a t ω) = score₂ t (s t ω) (a t ω)) :
  ∫ ω, ∑ t ∈ Finset.range n,
        (γ ^ t * Q t (s t ω) (a t ω)) • score₁ t (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, ∑ t ∈ Finset.range n,
        (γ ^ t * Q t (s t ω) (a t ω)) • score₂ t (s t ω) (a t ω) ∂(M θ) := by
  refine integral_congr_ae ?_
  have hAll : ∀ᵐ ω ∂(M θ), ∀ t,
      score₁ t (s t ω) (a t ω) = score₂ t (s t ω) (a t ω) := by
    rwa [ae_all_iff]
  filter_upwards [hAll] with ω hω
  refine Finset.sum_congr rfl fun t _ => ?_
  exact congrArg ((γ ^ t * Q t (s t ω) (a t ω)) • ·) (hω t)

/--
`h₁`: policy trajectory; `h₂`: joint `ℙ(a[0]∧s[0]) ≠ 0`; `h₃`/`h₄`: differentiable
conditional log-policy with uniformly bounded gradient (without them the statement is false).
Public `hP0` is omitted (recovered from joint ≠ 0). The bound on `∇V` over reachable pairs
`(t, x)` follows from time-homogeneity and finiteness of `S`. Densities w.r.t. counting measures.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : IsPolicyTrajectory M r s a)
  (h₂ : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) ≠ 0)
  (h₃ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₄ : sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t))
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.Measurable (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) = 𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _ _
  have h₁pol := h₁
  have h₂ne := h₂
  have h₃diff := h₃
  have h₄sup := h₄
  have : IsPolicyTrajectory M r s a := h₁
  classical
  have : IsProbabilityMeasure M.env.init := M.env.init_prob
  have : Nonempty S := nonempty_of_isProbabilityMeasure M.env.init
  have : Nonempty A := by
    have hsum := M.policy.sum_eq_one (0 : Θ) (Classical.arbitrary S)
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  -- joint ℙ(a[0]∧s[0]) = ℙ(s[0]) * ℙ(a[0]|s[0]); recover product form of joint h₂
  have hπ_mul : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
      (ℙ[M θ](s[0] = «s.bvar»[0])) * (ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0])) ≠ 0 := by
    intro θ «s.bvar» «a.bvar»
    have hj := h₂ θ «s.bvar» «a.bvar»
    have hJ : ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) =
        (M θ) ((a 0) ⁻¹' {«a.bvar»[0]} ∩ (s 0) ⁻¹' {«s.bvar»[0]}) := by
      rw [EqProb («π» := M θ) (x := (a 0, s 0))]
      congr 1
      ext ω
      simp [JointRandomSymbol, Prod.ext_iff]
    have hS₀ : ℙ[M θ](s[0] = «s.bvar»[0]) = (M θ) ((s 0) ⁻¹' {«s.bvar»[0]}) :=
      EqProb («π» := M θ) (x := s 0) «s.bvar»[0]
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
      rw [hJ, hS₀, hD]
      exact (ENNReal.mul_div_cancel hs0 (measure_ne_top (M θ) _)).symm
    rwa [← heq]
  have hP0_bind : ∀ θ («s.bvar» : ℕ ⇀ S), ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 := by
    intro θ «s.bvar»
    have ⟨hs0, _⟩ : ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 ∧
        ℙ[M θ](a[0] = (⟨fun _ => Classical.arbitrary A⟩ : ℕ ⇀ A)[0] | s[0] = «s.bvar»[0]) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ «s.bvar» ⟨fun _ => Classical.arbitrary A⟩)
      rwa [not_or] at h
    exact hs0
  have hP0raw : ∀ θ x, (M θ).real ((s 0) ⁻¹' {x}) ≠ 0 := by
    intro θ x
    have heqR : (ℙ[M θ](s[0] = x) : ℝ) = (M θ).real ((s 0) ⁻¹' {x}) := by
      rw [EqProb («π» := M θ) (x := s 0) x]
      rfl
    have heqE : ℙ[M θ](s[0] = x) = (M θ) ((s 0) ⁻¹' {x}) :=
      EqProb («π» := M θ) (x := s 0) x
    rw [← heqR]
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨hP0_bind θ ⟨fun _ => x⟩, heqE ▸ measure_ne_top (M θ) _⟩
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  -- bridge conditional-ℙ hyps to policy.prob facts expected by legacy body
  have h_pol_eq : ∀ θ' x u, (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) = M.policy.prob θ' x u := by
    intro θ' x u
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₁.stage_eq (hP θ' 0) (hP0raw θ' x),
      ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]
  have hDiffPol : ∀ x u, Differentiable ℝ (M.policy.prob · x u) := by
    intro x u
    exact (funext fun θ' => (h_pol_eq θ' x u).symm) ▸ h₃ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
  have hSupPol : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞ := by
    obtain ⟨C, hC⟩ := h₄
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
    have ⟨hs0, hcond⟩ : ℙ[M θ']((s 0) = y) ≠ 0 ∧
        ℙ[M θ']((a 0) = u | (s 0) = y) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ' ⟨fun _ => y⟩ ⟨fun _ => u⟩)
      rwa [not_or] at h
    have heqE : ℙ[M θ']((s 0) = y) = (M θ') ((s 0) ⁻¹' {y}) :=
      EqProb («π» := M θ') (x := s 0) y
    have hreal : (M θ').real ((s 0) ⁻¹' {y}) ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨heqE ▸ hs0, measure_ne_top (M θ') _⟩
    refine mul_ne_zero hreal ?_
    rw [← h_pol_eq θ' y u]
    refine ENNReal.toReal_ne_zero.mpr ⟨hcond, ?_⟩
    have hOF : ℙ[M θ']((a 0) = u | (s 0) = y) = ENNReal.ofReal (M.policy.prob θ' y u) :=
      ProbCond.eq.OfRealPol.of.Ne_0 h₁.stage_eq (hP θ' 0) (hP0raw θ' y)
    rw [hOF]
    apply ENNReal.ofReal_ne_top
  -- shadow legacy All_Eq / Diff / Sup / hP0 / hπ names for the rest of the body
  -- keep Fun stage_eq type (not naked) so All_Eq callers elaborate
  have h₁ := h₁pol.stage_eq
  have h₂ : ∀ s a, Differentiable ℝ (M.policy.prob · s a) := hDiffPol
  have h₃ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞ := hSupPol
  have hP0 : ∀ θ x, (M θ).real ((s 0) ⁻¹' {x}) ≠ 0 := hP0raw
  have hπ : ∀ θ y u, (M θ).real ((s 0) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0 := hπraw
  have h₃o := h₃
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₃
  have hfd : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    obtain ⟨C, hC⟩ := id h₃
    have hCb : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
    classical
    let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
    have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
        Qloc θ t («s.bvar» t) («a.bvar» t) =
          𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) :=
      fun _ _ _ _ => rfl
    let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
    have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
        Vloc θ t («s.bvar» t) =
          𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) :=
      fun _ _ _ => rfl
    -- inlined from former In_Ico1 (fderiv/CLM Q-score series)
    have h7grad :=
      GradExpectDotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
        (θ := θ) h₀ h₁ hQ_expect hV_expect h₂ h₃o hP0 hπ
    let Lgrad : StrongDual ℝ Θ ≃L[ℝ] Θ :=
      (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hLgrad : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = Lgrad φ := fun _ => rfl
    have hsumLgrad :
      Summable
        (fun t => γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
      have hs :=
        Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * C * |M.env.R|)
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      apply mul_le_mul_of_nonneg_left
      · apply (Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
          (M := M) h₁ h₂ hCb t).2
      · apply pow_nonneg h₀.1
    have h₇ :
      ∀ n,
        ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
          ∫ ω,
              ∑ t ∈ Finset.range n,
                (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                  fderiv ℝ
                    (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω)))
                    θ ∂(M θ) +
            γ ^ n •
              ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ) := by
      intro n
      have H := h7grad n
      -- Unwrap Expect form from In_Ico0 to integral form
      have hE_Lfun :
        (fun θ' ↦ 𝔼[r: M θ']((γ ^ (id : ℕ → ℕ)) @ r)) =
          (fun θ' ↦ ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ')) := by
        funext θ'
        have : PSpace (M θ') (AsPathRV.path r) :=
          PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
        exact ExpectDotPow_Id.eq.Integral_ExtDotPow_Id (M := M) (θ := θ') (γ := γ) (r := r)
      have hE_L :
        ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
          ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) := by
        simp only [gradient]
        exact congrArg (fun f ↦ (InnerProductSpace.toDual ℝ Θ).symm (fderiv ℝ f θ)) hE_Lfun
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
      have hRVθ :
        𝔼[s : M θ](∇[θ] (Vloc θ n (s n))) =
          ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
        expect_gradV_eq_integral (M := M) (θ := θ) (n := n)
          (V := fun θ' => Vloc θ' n) (s := s)
      -- GradExpect RHS is P-score Expect; unwrap then bridge ae to pol for fderiv goal
      have hSP : ∀ θ' t', SinglePSpace (M θ') (a t', s t') := fun θ' t' =>
        SinglePSpace.of.Measurable
          ((Random.Measurable.of.All_Eq.snd.snd h₁ t').prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t'))
      have : ∀ t, SinglePSpace (M θ) (a t, s t) := fun t => hSP θ t
      have hRQP :
        𝔼[s, a : M θ](∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t) (a t)) •
              ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) =
          ∫ ω, ∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
              ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) :=
        expect_finset_smul_score_eq_integral (M := M) (θ := θ) (γ := γ) (n := n)
          (Q := Qloc θ)
          (score := fun t x u => ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log)
          (s := s) (a := a)
      have hscore_n : ∀ t, ∀ᵐ ω ∂(M θ),
          ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) =
            ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log :=
        fun t => (gradLogProbCond_ae_eq_gradLogPol (M := M) (θ := θ) (r := r) (s := s) (a := a)
          h₁ h₂ h₃o hSP t).mono fun _ h => h.symm
      have hInt_pol_eq_P :
        ∫ ω, ∑ t ∈ Finset.range n,
              (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) =
          ∫ ω, ∑ t ∈ Finset.range n,
              (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) :=
        integral_finset_smul_score_eq_of_ae (M := M) (θ := θ) (γ := γ) (n := n)
          (Q := Qloc θ) (s := s) (a := a)
          (score₁ := fun t x u => ∇[θ] (Real.log (M.policy.prob θ x u)))
          (score₂ := fun t x u => ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log)
          hscore_n
      have HInt :
        ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
          ∫ ω, ∑ t ∈ Finset.range n,
              (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) +
            γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
        (hE_L.symm.trans (H.trans (congrArg₂ (· + ·) hRQP (congrArg (γ ^ n • ·) hRVθ)))).trans
          (congrArg₂ (· + ·) hInt_pol_eq_P.symm rfl)
      have hLfun_ico0 :
        (fun θ' ↦ ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ')) =
          fun θ' ↦ (γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ') := by
        funext θ'
        have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
          (All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ').mono fun ω h => by
            rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
            exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
        have hri : ∀ t, Integrable (fun ω ↦ γ ^ t * r t ω) (M θ') := fun t =>
          Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
        have hswap :
          ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') =
            ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
          rw [← integral_tsum_of_summable_integral_norm hri]
          · exact tsum_congr fun t => integral_const_mul _ _
          ·
            refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
              ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
            calc
              _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
                integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
              _ = γ ^ t * |M.env.R| := by simp
        refine Eq.trans ?_ (hswap.trans (by simp only [Dot.dot, Function.hPow_apply, id_eq]))
        · simp only [Dot.dot, Function.hPow_apply, id_eq]
      have hswap_grad :
        ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
          ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ)) := by
        simp only [gradient]
        exact congrArg (fun f ↦ (InnerProductSpace.toDual ℝ Θ).symm (fderiv ℝ f θ)) hLfun_ico0
      have H := hswap_grad.symm.trans HInt
      simp only [Dot.dot, Function.hPow_apply, id_eq, gradient] at H
      simp_rw [hLgrad] at H
      have hInt :
        Integrable
          (fun ω ↦
            ∑ t ∈ Finset.range n,
              (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                fderiv ℝ
                  (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)
          (M θ) :=
        integrable_finsetSum _ fun t _ =>
          Random.Integrable_Fun h₁ (M := M) θ t
            (fun y u =>
              (γ ^ t * Qloc θ t y u) •
                fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ)
      have hIntV :
        Integrable
          (fun ω ↦ fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ) (M θ) :=
        Random.Integrable_Fun h₁ (M := M) θ n
          (fun y _ => fderiv ℝ (fun θ' => Vloc θ' n y) θ)
      have hGetn :=
        GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ
      apply Lgrad.injective
      have := hsumLgrad
      have := hInt
      have := hIntV
      rw [← hGetn.fderiv]
      refine H.trans ?_
      refine Eq.trans ?_ (map_add Lgrad _ _).symm
      congr 1
      ·
        refine Eq.trans ?_ (Lgrad.integral_comp_comm _)
        congr 1
        refine funext fun ω =>
          Eq.trans (Finset.sum_congr rfl fun t _ => (map_smul Lgrad _ _).symm)
            (_root_.map_sum Lgrad _ _).symm
      ·
        refine Eq.trans (congrArg (fun z => γ ^ n • z) (Lgrad.integral_comp_comm _)) ?_
        exact (map_smul Lgrad (γ ^ n) _).symm
    obtain ⟨B, hB⟩ :=
      BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ (hP0 θ)
    have h₉ : ∀ n, ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖ ≤ max B 0 := by
      intro n
      rw [Integral.eq.Sum_SMul h₁ (M := M) θ n (fun y => fderiv ℝ (fun θ' => Vloc θ' n y) θ)]
      calc
        _ ≤ ∑ y, ‖(M θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => Vloc θ' n y) θ‖ :=
          norm_sum_le _ _
        _ ≤ ∑ y, (M θ).real (s n ⁻¹' {y}) * max B 0 := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
          if hy : (M θ).real (s n ⁻¹' {y}) = 0 then
            rw [hy, zero_mul, zero_mul]
          else
            exact mul_le_mul_of_nonneg_left ((hB ⟨(n, y), hy, rfl⟩).trans (le_max_left _ _)) measureReal_nonneg
        _ = max B 0 := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
    have hγ : |γ| < 1 := by
      rw [abs_of_nonneg h₀.1]
      apply h₀.2
    have h₁₀ :
      Tendsto (fun n => γ ^ n * ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖) atTop (𝓝 0) :=
      Eq_0.Lim.of.LtAbs.GtInftySup hγ
        ⟨max B 0, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (h₉ n)⟩
    have h₁₁ :
      Tendsto (fun n => γ ^ n • ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine h₁₀.congr fun n => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
    have h₁₂ : ∀ t, ‖∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
        Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0) := by
      intro t
      rw [Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₂ θ t (fun y u => Qloc θ t y u)]
      calc
        _ ≤ ∑ y, ‖(M θ).real (s t ⁻¹' {y}) •
            ∑ u, Qloc θ t y u • fderiv ℝ (fun θ' => M.policy.prob θ' y u) θ‖ :=
          norm_sum_le _ _
        _ ≤ ∑ y, (M θ).real (s t ⁻¹' {y}) * (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum (g := fun _ => (1 - γ)⁻¹ * |M.env.R| * max C 0) fun u _ => ?_).trans_eq ?_
          ·
            rw [norm_smul]
            exact mul_le_mul (NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t y u)
              ((hCb θ y u).trans (le_max_left _ _)) (norm_nonneg _) hq
          ·
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = _ := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
    have h₁₃ : Summable (fun t => γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) := by
      have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right
        (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0))
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h₁₂ t) (pow_nonneg h₀.1 t)
    have h₁₄ : ∀ n, ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
        ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      intro n
      rw [integral_finsetSum _ fun t _ => Random.Integrable_Fun h₁ (M := M) θ t
        (fun y u => (γ ^ t * Qloc θ t y u) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ)]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp_rw [mul_smul]
      exact integral_smul _ _
    have h₁₅ := h₁₃.hasSum.tendsto_sum_nat.add h₁₁
    rw [add_zero] at h₁₅
    have hQseries :
      ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
        ∑' t, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n => ?_) h₁₅
      rw [h₇ n, h₁₄ n]
    rw [hQseries]
    refine tsum_congr fun t => congrArg (fun z => γ ^ t • z) ?_
    -- Expect-surface LIE → observation integrals
    let ψ : S → A → (Θ →L[ℝ] ℝ) := fun x u =>
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x u)) θ
    have hlie :=
      ExpectSMul.eq.ExpectSMulExpectCond.of.All_Eq.In_Ico (M := M) h₀ h₁ θ t ψ
    have hsa : Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) :=
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        ((measurable_pi_apply t).comp measurable_snd)
    have hsa3 : Measurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦ (p.2.1 t, p.2.2 t) :=
      ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
    have hGpath : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
        ((γ ^ (id : ℕ → ℕ)) @ fun k ↦ p.1 (t + k)) :=
      (Measurable_G.of.All_Measurable
        (r := fun j (p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A))) => p.1 j)
        (fun j => (measurable_pi_apply j).comp measurable_fst) γ t).stronglyMeasurable
    have hψpath3 : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
        ψ (p.2.1 t) (p.2.2 t) :=
      StronglyMeasurable.comp_measurable
        (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa3
    have hQpath : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = p.1 t ∧ a t = p.2 t) :=
      ((measurable_of_countable fun q : S × A =>
          𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = q.1 ∧ a t = q.2)).comp hsa).stronglyMeasurable
    have hψpath2 : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦ ψ (p.1 t) (p.2 t) :=
      StronglyMeasurable.comp_measurable
        (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa
    have hG :
      𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ψ (s t) (a t)) =
        ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) := by
      have : ∀ θ', PSpace (M θ') (AsPathRV.path r) :=
        fun _ => PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ j).aemeasurable⟩)
      rw [Expectation.ofRV, expectation_bochner]
      have hx : AEMeasurable
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a) (M θ) :=
        PSpace.aemeasurable
      refine (integral_map hx (hGpath.smul hψpath3).aestronglyMeasurable).trans ?_
      simp only [JointRandomSymbol, AsPathRV.path_process]
      rfl
    -- ∫Q = 𝔼[Q] = 𝔼[G] = ∫G
    refine Eq.symm ?_ |>.trans (hlie.symm.trans hG)
    ·
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ j).aemeasurable⟩)
      have : ∀ θ', PSpace (M θ') (AsPathRV.path r) :=
        fun _ => PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₁ j).aemeasurable⟩)
      rw [Expectation.ofRV, expectation_bochner]
      have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
        PSpace.aemeasurable
      refine (integral_map hx (hQpath.smul hψpath2).aestronglyMeasurable).trans ?_
      simp only [JointRandomSymbol, AsPathRV.path_process]
      change ∫ ω, Qloc θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) =
        ∫ ω, Qloc θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
      rfl
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃o t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  have hold : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) := by
    rw [hfd]
    refine tsum_congr fun t => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hscore t] with ω hω
    rw [hω]
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  -- almost sure bound of the discounted return from `t`
  have hA' : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  -- the reward series
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc
        _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
          integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hA_sup : ∀ᵐ ω ∂(M θ),
      sup[t] |((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω))| < ∞ := by
    filter_upwards [hA'] with ω h
    refine ⟨(1 - γ)⁻¹ * |M.env.R|, ?_⟩
    rintro _ ⟨t, rfl⟩
    simpa only [Dot.dot, Function.hPow_apply, id_eq, Real.norm_eq_abs] using h t
  have hRb := @Integral_Dot_FunSMul_GradLogProbCond.eq.ExpectDot.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico
    _ _ _ _ _ _ _ _ _ _ _ _ M θ γ (fun r _ _ k => r k) ⟨r⟩ ⟨s⟩ ⟨a⟩ h₀ h₁pol h₂ne
    (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hA_sup h₃diff h₄sup
  have hL2GradDot :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∑' t, γ ^ t • ∫ ω,
        ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ)) =
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
        ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom_apply, gradient]
    rw [hL, L.map_tsum]
    refine tsum_congr fun t => ?_
    rw [map_smul]
    congr 1
    rw [← L.integral_comp_comm]
    refine congrArg _ (funext fun ω => ?_)
    rw [map_smul, hL]
  -- Dot_Integral → Integral_Dot (swap formerly inside In_Ico0)
  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖ :=
    ⟨_, rfl⟩
  have hsc : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal‖ ≤ Ms := by
    intro t
    filter_upwards [hscore t] with ω hω
    rw [gradient, LinearIsometryEquiv.norm_map, hω, hMs]
    exact Finset.single_le_sum (f := fun q : S × A => ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))
  set Bret : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hFb : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ≤ γ ^ t * (Bret * Ms) := by
    intro t
    filter_upwards [hA', hsc t] with ω h1 h2
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hdot : ‖((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω))‖ = ‖∑' k, γ ^ k * r (t + k) ω‖ := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hdot]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h1 t) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (h1 t))) (pow_nonneg h₀.1 t)
  have hg : ∀ t, StronglyMeasurable fun ω =>
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal := fun t =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        gradient (fun θ' => Real.log (ℙ[M θ']((a t) = p.2 | (s t) = p.1)).toReal) θ)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))
  have hint : ∀ t, Integrable (fun ω =>
      γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)) (M θ) :=
    fun t => Integrable.of_bound ((hg t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFb t)
  have hsumI : Summable fun t => ∫ ω,
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (Bret * Ms))
    calc
      _ ≤ ∫ _, γ ^ t * (Bret * Ms) ∂(M θ) :=
        integral_mono_ae (hint t).norm (integrable_const _) (hFb t)
      _ = γ ^ t * (Bret * Ms) := by simp
  have hSwap :
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
      ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
    ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) ∂(M θ) := by
    have hLHS :
      (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
        ∑' t, γ ^ t • ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ) := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    have hRHS : ∀ ω,
        ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) =
        ∑' t, γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) := by
      intro ω
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hLHS]
    simp_rw [hRHS]
    rw [← integral_tsum_of_summable_integral_norm hint hsumI]
    exact tsum_congr fun t => (integral_smul (γ ^ t) _).symm
  have hL2Grad := hL2GradDot.trans hSwap
  refine Eq.trans ?_ ((congrArg L hold).trans (hL2Grad.trans hRb))
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ).fderiv, gradient, hL]
  congr 2
  funext θ'
  have hr' : ∀ t, PSpace (M θ') (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have hpr' : PSpace (M θ') (AsPathRV.path r) :=
    PSpace_Path.of.All_PSpace hr'
  refine Eq.trans ?_ (hRint θ')
  simp only [Dot.dot]
  rw [Expectation.ofRV, expectation_real]
  refine (integral_map hpr'.aemeasurable ?_).trans ?_
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
  · rfl

/--
Unbiased advantage estimate: with the advantage
(rewards are bounded by the environment, so both series may be taken inside `𝔼`).
and the baseline term `𝔼[V(s[t]) • ∇ log π(a[t] | s[t])]` vanishes (zero expected score).
The bounds on `V` and `∇V` over the reachable pairs `ℙ(s[t] = x) ≠ 0` are not assumed: `|V|` is bounded
by the reward bound (`NormV.le.MulSub1Abs_R.of.In_Ico`), and `∇V` by time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`).
Densities are taken w.r.t. the counting measures (`CountableMeasure`), so
`ℙ[M θ](s[t] = x)` is the point mass and `ℙ[M θ](a[t] = u | s[t] = x)` is the policy
`π_θ(u | x)` at reachable states; the `SinglePSpace` facts the `ℙ` terms need follow from `CountableMeasure.measure_eq_count`.
-/
@[path]
private lemma advantage
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : IsPolicyTrajectory M r s a)
  (h₂ : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) ≠ 0)
  (h₃ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₄ : sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t))
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.Measurable (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ _ V_θ
  have h₁pol := h₁
  have h₂ne := h₂
  have h₃diff := h₃
  have h₄sup := h₄
  have : IsPolicyTrajectory M r s a := h₁
  classical
  have : IsProbabilityMeasure M.env.init := M.env.init_prob
  have : Nonempty S := nonempty_of_isProbabilityMeasure M.env.init
  have : Nonempty A := by
    have hsum := M.policy.sum_eq_one (0 : Θ) (Classical.arbitrary S)
    by_contra h
    have : IsEmpty A := not_nonempty_iff.mp h
    simp [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  -- joint ℙ(a[0]∧s[0]) = ℙ(s[0]) * ℙ(a[0]|s[0]); recover product form of joint h₂
  have hπ_mul : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
      (ℙ[M θ](s[0] = «s.bvar»[0])) * (ℙ[M θ](a[0] = «a.bvar»[0] | s[0] = «s.bvar»[0])) ≠ 0 := by
    intro θ «s.bvar» «a.bvar»
    have hj := h₂ θ «s.bvar» «a.bvar»
    have hJ : ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) =
        (M θ) ((a 0) ⁻¹' {«a.bvar»[0]} ∩ (s 0) ⁻¹' {«s.bvar»[0]}) := by
      rw [EqProb («π» := M θ) (x := (a 0, s 0))]
      congr 1
      ext ω
      simp [JointRandomSymbol, Prod.ext_iff]
    have hS₀ : ℙ[M θ](s[0] = «s.bvar»[0]) = (M θ) ((s 0) ⁻¹' {«s.bvar»[0]}) :=
      EqProb («π» := M θ) (x := s 0) «s.bvar»[0]
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
      rw [hJ, hS₀, hD]
      exact (ENNReal.mul_div_cancel hs0 (measure_ne_top (M θ) _)).symm
    rwa [← heq]
  have hP0_bind : ∀ θ («s.bvar» : ℕ ⇀ S), ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 := by
    intro θ «s.bvar»
    have ⟨hs0, _⟩ : ℙ[M θ](s[0] = «s.bvar»[0]) ≠ 0 ∧
        ℙ[M θ](a[0] = (⟨fun _ => Classical.arbitrary A⟩ : ℕ ⇀ A)[0] | s[0] = «s.bvar»[0]) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ «s.bvar» ⟨fun _ => Classical.arbitrary A⟩)
      rwa [not_or] at h
    exact hs0
  have hP0raw : ∀ θ x, (M θ).real ((s 0) ⁻¹' {x}) ≠ 0 := by
    intro θ x
    have heqR : (ℙ[M θ](s[0] = x) : ℝ) = (M θ).real ((s 0) ⁻¹' {x}) := by
      rw [EqProb («π» := M θ) (x := s 0) x]
      rfl
    have heqE : ℙ[M θ](s[0] = x) = (M θ) ((s 0) ⁻¹' {x}) :=
      EqProb («π» := M θ) (x := s 0) x
    rw [← heqR]
    apply ENNReal.toReal_ne_zero.mpr
    exact ⟨hP0_bind θ ⟨fun _ => x⟩, heqE ▸ measure_ne_top (M θ) _⟩
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  -- bridge conditional-ℙ hyps to policy.prob facts expected by legacy body
  have h_pol_eq : ∀ θ' x u, (ℙ[M θ']((a 0) = u | (s 0) = x) : ℝ) = M.policy.prob θ' x u := by
    intro θ' x u
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₁.stage_eq (hP θ' 0) (hP0raw θ' x),
      ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]
  have hDiffPol : ∀ x u, Differentiable ℝ (M.policy.prob · x u) := by
    intro x u
    exact (funext fun θ' => (h_pol_eq θ' x u).symm) ▸ h₃ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
  have hSupPol : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞ := by
    obtain ⟨C, hC⟩ := h₄
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
    have ⟨hs0, hcond⟩ : ℙ[M θ']((s 0) = y) ≠ 0 ∧
        ℙ[M θ']((a 0) = u | (s 0) = y) ≠ 0 := by
      have h := mt mul_eq_zero.mpr (hπ_mul θ' ⟨fun _ => y⟩ ⟨fun _ => u⟩)
      rwa [not_or] at h
    have heqE : ℙ[M θ']((s 0) = y) = (M θ') ((s 0) ⁻¹' {y}) :=
      EqProb («π» := M θ') (x := s 0) y
    have hreal : (M θ').real ((s 0) ⁻¹' {y}) ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨heqE ▸ hs0, measure_ne_top (M θ') _⟩
    refine mul_ne_zero hreal ?_
    rw [← h_pol_eq θ' y u]
    refine ENNReal.toReal_ne_zero.mpr ⟨hcond, ?_⟩
    have hOF : ℙ[M θ']((a 0) = u | (s 0) = y) = ENNReal.ofReal (M.policy.prob θ' y u) :=
      ProbCond.eq.OfRealPol.of.Ne_0 h₁.stage_eq (hP θ' 0) (hP0raw θ' y)
    rw [hOF]
    apply ENNReal.ofReal_ne_top
  -- shadow legacy All_Eq / Diff / Sup / hP0 / hπ names for the rest of the body
  -- keep Fun stage_eq type (not naked) so All_Eq callers elaborate
  have h₁ := h₁pol.stage_eq
  have h₂ : ∀ s a, Differentiable ℝ (M.policy.prob · s a) := hDiffPol
  have h₃ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞ := hSupPol
  have hP0 : ∀ θ x, (M θ).real ((s 0) ⁻¹' {x}) ≠ 0 := hP0raw
  have hπ : ∀ θ y u, (M θ).real ((s 0) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0 := hπraw
  let G : (ℕ → ℝ × S × A) → Θ := fun ω => ∑' t, γ ^ t • ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) • ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log)
  have hG : PSpace (M θ) G := ⟨(StronglyMeasurable.tsum fun t => (StronglyMeasurable.smul
      (Measurable.tsum fun k =>
        (((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add (((measurable_of_countable (fun x : S => M.V θ γ (t + k + 1) x)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
          ((measurable_of_countable (fun x : S => M.V θ γ (t + k) x)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        ∇[θ] (ℙ[M θ]((a t) = p.2 | (s t) = p.1) : ℝ).log)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).const_smul (γ ^ t)).aestronglyMeasurable.aemeasurable⟩
  have hPs : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.Measurable (Random.Measurable.of.All_Eq.snd.fst h₁ t)
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hVbd : ∀ t x, |Vloc θ t x| ≤ (1 - γ)⁻¹ * |M.env.R| := fun t x => by
    simpa only [Real.norm_eq_abs] using NormV.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t x
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ t x, |Vloc θ t x| ≤ B := ⟨_, hVbd⟩
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) → (M.V θ' γ t x = Vloc θ' t x) := fun θ' t x _ =>
    rfl
  have key : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    -- V is the conditional expectation, so V _ _ ⟨fun _ => x⟩ = Vloc _ _ x definitionally
    change ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * Vloc θ (t + k + 1) (s (t + k + 1) ω) -
        Vloc θ (t + k) (s (t + k) ω))) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)
    congr 1
    funext t
    congr 1
    have h₉ : ∀ᵐ ω ∂(M θ), ∑' k, γ ^ k * (r (t + k) ω + γ * Vloc θ (t + k + 1) (s (t + k + 1) ω) -
        Vloc θ (t + k) (s (t + k) ω)) = (∑' k, γ ^ k * r (t + k) ω) - Vloc θ t (s t ω) := by
      filter_upwards [All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico (M := M) h₀ h₁ θ t] with ω hG
      have hb : ∀ k, |Vloc θ k (s k ω)| ≤ B := fun k => hBd k _
      set b : ℕ → ℝ := fun k => γ ^ k * Vloc θ (t + k) (s (t + k) ω) with hbd
      have hlim : Tendsto b atTop (𝓝 0) :=
        Eq_0.Lim.of.LtAbs.GtInftySup (x := fun k => Vloc θ (t + k) (s (t + k) ω))
          (by simpa [abs_of_nonneg h₀.1] using h₀.2) ⟨B, by rintro _ ⟨k, rfl⟩; exact hb (t + k)⟩
      have he : ∀ k, γ ^ k * (r (t + k) ω + γ * Vloc θ (t + k + 1) (s (t + k + 1) ω) -
          Vloc θ (t + k) (s (t + k) ω)) = γ ^ k * r (t + k) ω + (b (k + 1) - b k) := fun k => by
        simp only [hbd]
        rw [show t + (k + 1) = t + k + 1 by omega]
        ring
      have hbs : Summable (fun k => b (k + 1) - b k) := by
        refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (2 * B))
          fun k => ?_
        calc
          _ ≤ ‖b (k + 1)‖ + ‖b k‖ := norm_sub_le _ _
          _ ≤ γ ^ k * B + γ ^ k * B := by
            simp only [hbd]
            rw [norm_mul, norm_mul, norm_pow, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs,
              Real.norm_eq_abs]
            exact add_le_add (mul_le_mul (pow_le_pow_of_le_one h₀.1 h₀.2.le (Nat.le_succ k))
              (hb _) (abs_nonneg _) (pow_nonneg h₀.1 k)) (mul_le_mul_of_nonneg_left (hb _) (pow_nonneg h₀.1 k))
          _ = γ ^ k * (2 * B) := by ring
      have hbsum : ∑' k, (b (k + 1) - b k) = - b 0 := by
        refine tendsto_nhds_unique hbs.hasSum.tendsto_sum_nat ?_
        simp_rw [Finset.sum_range_sub]
        simpa using hlim.sub_const (b 0)
      simp_rw [he]
      rw [hG.1.summable.tsum_add hbs, hbsum]
      simp only [hbd, pow_zero, one_mul, add_zero]
      ring
    symm
    calc
      _ = ∫ ω, ((∑' k, γ ^ k * r (t + k) ω) - Vloc θ t (s t ω)) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
        integral_congr_ae (h₉.mono fun ω h => by dsimp only; rw [h])
      _ = (∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) -
          ∫ ω, Vloc θ t (s t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
        simp_rw [sub_smul]
        exact integral_sub (Integrable.of.In_Ico (M := M) h₀ h₁ θ t (fun y u => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ))
          (Integrable_Fun h₁ (M := M) θ t (fun y u => Vloc θ t y • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ))
      _ = _ := by
        have h := Integral_SMul.eq.Zero.of.All_Differentiable_Prob (M := M) h₁ h₂ θ t (fun y => Vloc θ t y)
        beta_reduce at h
        rw [h, sub_zero]
  have holdRA : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) := by
    have e1 : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
        ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      refine tsum_congr fun t => ?_
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hscore t] with ω hω
      rw [hω]
    refine e1.trans (key.trans ?_)
    refine tsum_congr fun t => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hscore t] with ω hω
    rw [hω]
  -- almost sure bound of the advantage, uniform in `t`
  have hAdv : ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))‖ ≤
        (1 - γ)⁻¹ * (|M.env.R| + γ * B + B) := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ, AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hr hR t
    have hb : ∀ n, |M.V θ γ n (s n ω)| ≤ B := fun n => by
      rw [hVr θ n _ (hR n)]
      exact hBd n _
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 k)
    calc
      _ ≤ ‖r (t + k) ω‖ + ‖γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω)‖ + ‖M.V θ γ (t + k) (s (t + k) ω)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |M.env.R| + γ * B + B := by
        rw [norm_mul, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (add_le_add (hr _) (mul_le_mul_of_nonneg_left (hb _) h₀.1)) (hb _)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  have hT : ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k))) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) :=
    main h₀ h₁pol h₂ne h₃diff h₄sup
  have hRae : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  have hRae_sup : ∀ᵐ ω ∂(M θ),
      sup[t] |((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω))| < ∞ := by
    filter_upwards [hRae] with ω h
    refine ⟨(1 - γ)⁻¹ * |M.env.R|, ?_⟩
    rintro _ ⟨t, rfl⟩
    simpa only [Dot.dot, Function.hPow_apply, id_eq, Real.norm_eq_abs] using h t
  have hRb := @ExpectDot.eq.Integral_Dot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico
    _ _ _ _ _ _ _ _ _ _ _ _ M θ γ (fun r _ _ k => r k) ⟨r⟩ ⟨s⟩ ⟨a⟩ h₀ h₁pol h₂ne
    (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hRae_sup h₃diff h₄sup
  have hL2GradRDot :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∑' t, γ ^ t • ∫ ω,
        (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ)) =
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
        ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) := by
    let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
    have hdot : ∀ t ω, (∑' k, γ ^ k * r (t + k) ω) =
        ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) := by
      intro t ω; simp only [Dot.dot, Function.hPow_apply, id_eq]
    simp only [Dot.dot, Function.hPow_apply, id_eq, gradient]
    simp_rw [hdot]
    rw [hL, L.map_tsum]
    refine tsum_congr fun t => ?_
    rw [map_smul]
    congr 1
    rw [← L.integral_comp_comm]
    refine congrArg _ (funext fun ω => ?_)
    rw [map_smul, hL]
  -- Dot_Integral → Integral_Dot for reward score series
  obtain ⟨MsR, hMsR⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖ :=
    ⟨_, rfl⟩
  have hscR : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal‖ ≤ MsR := by
    intro t
    filter_upwards [hscore t] with ω hω
    rw [gradient, LinearIsometryEquiv.norm_map, hω, hMsR]
    exact Finset.single_le_sum (f := fun q : S × A => ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))
  set BretR : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hFbR : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ≤ γ ^ t * (BretR * MsR) := by
    intro t
    filter_upwards [hRae, hscR t] with ω h1 h2
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hdot : ‖((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω))‖ = ‖∑' k, γ ^ k * r (t + k) ω‖ := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hdot]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h1 t) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (h1 t))) (pow_nonneg h₀.1 t)
  have hgR : ∀ t, StronglyMeasurable fun ω =>
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal := fun t =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (Random.Measurable.of.All_Eq.fst h₁ (t + k)).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        gradient (fun θ' => Real.log (ℙ[M θ']((a t) = p.2 | (s t) = p.1)).toReal) θ)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))
  have hintR : ∀ t, Integrable (fun ω =>
      γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)) (M θ) :=
    fun t => Integrable.of_bound ((hgR t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFbR t)
  have hsumR : Summable fun t => ∫ ω,
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BretR * MsR))
    calc
      _ ≤ ∫ _, γ ^ t * (BretR * MsR) ∂(M θ) :=
        integral_mono_ae (hintR t).norm (integrable_const _) (hFbR t)
      _ = γ ^ t * (BretR * MsR) := by simp
  have hSwapR :
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
      ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
    ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) ∂(M θ) := by
    have hLHS :
      (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
        ∑' t, γ ^ t • ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ) := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    have hRHS : ∀ ω,
        ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) =
        ∑' t, γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω)) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) := by
      intro ω
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hLHS]
    simp_rw [hRHS]
    rw [← integral_tsum_of_summable_integral_norm hintR hsumR]
    exact tsum_congr fun t => (integral_smul (γ ^ t) _).symm
  have hL2GradR := hL2GradRDot.trans hSwapR
  refine hT.trans (hRb.trans (hL2GradR.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm holdRA).trans ?_)))
  have hAdv_sup : ∀ᵐ ω ∂(M θ),
      sup[t] |((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ =>
        r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω)))| < ∞ := by
    filter_upwards [hAdv] with ω h
    refine ⟨(1 - γ)⁻¹ * (|M.env.R| + γ * B + B), ?_⟩
    rintro _ ⟨t, rfl⟩
    simpa only [Dot.dot, Function.hPow_apply, id_eq, Real.norm_eq_abs] using h t
  have hAdvExp :=
    @Integral_Dot_FunSMul_GradLogProbCond.eq.ExpectDot.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico
    _ _ _ _ _ _ _ _ _ _ _ _ M θ γ
    (fun r s _ k => r k + γ * M.V θ γ (k + 1) (s (k + 1)) - M.V θ γ k (s k))
    ⟨r⟩ ⟨s⟩ ⟨a⟩ h₀ h₁pol h₂ne
    (fun k => ((Random.Measurable.of.All_Eq.fst h₁ k).add (((measurable_of_countable (fun x : S => M.V θ γ (k + 1) x)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (fun x : S => M.V θ γ k x)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ k)))
    hAdv_sup h₃diff h₄sup
  have hL2GradAdvDot :
    (InnerProductSpace.toDual ℝ Θ).symm
      (∑' t, γ ^ t • ∫ ω,
        (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ)) =
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
        ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ =>
          r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) := by
    let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
    have hdot : ∀ t ω,
        (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) =
        ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ =>
          r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) := by
      intro t ω; simp only [Dot.dot, Function.hPow_apply, id_eq]
    simp only [Dot.dot, Function.hPow_apply, id_eq, gradient]
    simp_rw [hdot]
    rw [hL, L.map_tsum]
    refine tsum_congr fun t => ?_
    rw [map_smul]
    congr 1
    rw [← L.integral_comp_comm]
    refine congrArg _ (funext fun ω => ?_)
    rw [map_smul, hL]
  -- Dot_Integral → Integral_Dot for advantage score series
  obtain ⟨MsA, hMsA⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖ :=
    ⟨_, rfl⟩
  have hscA : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal‖ ≤ MsA := by
    intro t
    filter_upwards [hscore t] with ω hω
    rw [gradient, LinearIsometryEquiv.norm_map, hω, hMsA]
    exact Finset.single_le_sum (f := fun q : S × A => ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' q.1 q.2)) θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))
  set BretA : ℝ := (1 - γ)⁻¹ * (|M.env.R| + γ * B + B)
  have hFbA : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ≤ γ ^ t * (BretA * MsA) := by
    intro t
    filter_upwards [hAdv, hscA t] with ω h1 h2
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hdot : ‖((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω)))‖ =
        ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))‖ := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hdot]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h1 t) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (h1 t))) (pow_nonneg h₀.1 t)
  have hgA : ∀ t, StronglyMeasurable fun ω =>
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal := fun t =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add
          (((measurable_of_countable (fun x : S => M.V θ γ (t + k + 1) x)).comp
            (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
          ((measurable_of_countable (fun x : S => M.V θ γ (t + k) x)).comp
            (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        gradient (fun θ' => Real.log (ℙ[M θ']((a t) = p.2 | (s t) = p.1)).toReal) θ)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))
  have hintA : ∀ t, Integrable (fun ω =>
      γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)) (M θ) :=
    fun t => Integrable.of_bound ((hgA t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFbA t)
  have hsumA : Summable fun t => ∫ ω,
      ‖γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BretA * MsA))
    calc
      _ ≤ ∫ _, γ ^ t * (BretA * MsA) ∂(M θ) :=
        integral_mono_ae (hintA t).norm (integrable_const _) (hFbA t)
      _ = γ ^ t * (BretA * MsA) := by simp
  have hSwapA :
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
      ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
    ∫ ω,
      ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) ∂(M θ) := by
    have hLHS :
      (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ)) =
        ∑' t, γ ^ t • ∫ ω,
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal ∂(M θ) := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    have hRHS : ∀ ω,
        ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          ((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
            ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) =
        ∑' t, γ ^ t • (((γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ => r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) - M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal) := by
      intro ω
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [hLHS]
    simp_rw [hRHS]
    rw [← integral_tsum_of_summable_integral_norm hintA hsumA]
    exact tsum_congr fun t => (integral_smul (γ ^ t) _).symm
  have hL2GradAdv := hL2GradAdvDot.trans hSwapA
  refine (hL2GradAdv.trans hAdvExp).trans ?_
  -- V_θ[t] s[t:] k = M.V θ γ (t + k) (s (t + k))
  have eqVθ : ∀ t (δ : ℕ → S) k, V_θ[t] δ k = M.V θ γ (t + k) (δ k) := by
    intro t δ k
    simp [V_θ]
  have hδθ : ∀ (s : ℕ → S) (r : ℕ → ℝ) (t : ℕ),
      (fun k => r (t + k) + γ * M.V θ γ (t + k + 1) (s (t + k + 1)) - M.V θ γ (t + k) (s (t + k))) =
        r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:] := by
    intro s r t
    funext k
    have hk : t + k + 1 = t + 1 + k := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hk, eqVθ t s[t:] k, eqVθ (t + 1) s[t + 1:] k]
    simp only [Function.getSliceFrom_apply]
  change
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k) + γ * M.V θ γ (t + k + 1) (s (t + k + 1)) -
          M.V θ γ (t + k) (s (t + k)))) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log)) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
          ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log))
  refine congrArg
    (Expectation.ofRV (M θ)
      (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
  funext integ
  dsimp
  congr 1
  funext t
  congr 1
  exact congrArg (fun δ => Dot.dot (γ ^ (id : ℕ → ℕ)) δ)
    (hδθ (fun j => integ.2.1 j) (fun j => integ.1 j) t)


-- created on 2026-10-21
-- updated on 2026-10-23

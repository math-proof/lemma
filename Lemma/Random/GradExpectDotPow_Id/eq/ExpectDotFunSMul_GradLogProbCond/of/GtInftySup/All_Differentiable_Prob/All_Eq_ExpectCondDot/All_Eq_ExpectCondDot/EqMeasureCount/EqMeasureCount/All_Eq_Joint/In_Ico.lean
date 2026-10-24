import Lemma.Random.GradExpectDotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Sum_RealPreimageS.eq.One
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure Set
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 625000


-- Path-binder form of the discounted Q-score integral.
lemma expect_smul_grad_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ}
  {Q : ℕ → S → A → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (_ : ∀ t, (· t) = (r t, s t, a t))
  [PSpace (M θ) (AsPathRV.path s)]
  [PSpace (M θ) (AsPathRV.path a)] :
  𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      Q t (s t) (a t) • ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) =
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      Q t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) ∂(M θ) := by
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx ?_).trans ?_
  ·
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t => ?_).aestronglyMeasurable
    exact StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦
        (γ ^ t) • Q t q.1 q.2 • ∇[θ] (Real.log (M.policy.prob θ q.1 q.2)))
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  ·
    simp only [JointRandomSymbol, AsPathRV.path_process, Dot.dot, Function.hPow_apply, id_eq]


/-- Path-binder finset Q-score Expect = observation integral. -/
private lemma expect_finset_smul_gradLogProb_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : ℕ → S → A → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (_ : ∀ t, (· t) = (r t, s t, a t))
  [PSpace (M θ) (AsPathRV.path s)]
  [PSpace (M θ) (AsPathRV.path a)] :
  𝔼[s, a : M θ](∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t) (a t)) • ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) =
    ∫ ω, ∑ t ∈ Finset.range n,
      (γ ^ t * Q t (s t ω) (a t ω)) •
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) := by
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx ?_).trans ?_
  ·
    refine (Finset.stronglyMeasurable_fun_sum (Finset.range n) fun t _ => ?_).aestronglyMeasurable
    exact StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦
        (γ ^ t * Q t q.1 q.2) • ∇[θ] (Real.log (M.policy.prob θ q.1 q.2)))
      StronglyMeasurable.of_discrete
      (show Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) from
        ((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp measurable_snd))
  ·
    simp only [JointRandomSymbol, AsPathRV.path_process]

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
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
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

/-- The discounted score integral for `fderiv`, split out so elaboration has its own heartbeat budget. -/
private lemma fderiv_tsum_eq_integral_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP0 : ∀ θ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0)
  (hπ : ∀ θ y u, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0) :
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∑' t, γ ^ t • ∫ ω, Q θ t (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable.Measurable (Random.Measurable.of.All_Eq.snd.snd h₁ t) (Random.Measurable.of.All_Eq.snd.fst h₁ t)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (s)) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (a)) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hQ : Q = Qloc := funext fun θ => funext fun t => funext fun x => funext fun u =>
    h₂ θ t (fun _ ↦ x) (fun _ ↦ u)
  have hV : V = Vloc := funext fun θ => funext fun t => funext fun x =>
    h₃ θ t (fun _ ↦ x)
  subst hQ hV
  have hfd :
    ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)
      := by
    have h5n := h₅
    have h5fd := h₅
    simp only [gradient, LinearIsometryEquiv.norm_map] at h5fd
    obtain ⟨Cfd, hCfd⟩ := id h5fd
    have h8fd : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cfd := fun θ x u => hCfd ⟨(θ, x, u), rfl⟩
    have h7grad :=
      GradExpectDotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
        (θ := θ) h₀ h₁ h₂ h₃ h₄ h5n hP0 hπ
    let Lgrad : StrongDual ℝ Θ ≃L[ℝ] Θ :=
      (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hLgrad : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = Lgrad φ := fun _ => rfl
    have hsumLgrad :
        Summable
          (fun t => γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
      have hs :=
        Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * Cfd * |M.env.R|)
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left
        ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
            (M := M) h₁ h₄ h8fd t).2 θ)
        (pow_nonneg h₀.1 t)
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
        have : PSpace (M θ') (AsPathRV.path (r)) :=
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
      -- GradExpect RHS is ℙ-score Expect; unwrap then bridge ae to pol for fderiv goal
      have hSP : ∀ θ' t', SinglePSpace (M θ') (a t', s t') := fun θ' t' =>
        SinglePSpace.of.Measurable.Measurable
          (Random.Measurable.of.All_Eq.snd.snd h₁ t') (Random.Measurable.of.All_Eq.snd.fst h₁ t')
      have : ∀ t, SinglePSpace (M θ) (a t, s t) := fun t => hSP θ t
      have hRQP :
        𝔼[s, a : M θ](∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t) (a t)) •
              ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) =
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
          h₁ h₄ h₅ hSP t).mono fun _ h => h.symm
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
        have hL1 : ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ') =
          ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') := by
          simp only [Dot.dot, Function.hPow_apply, id_eq]
        exact hL1.trans (hswap.trans (by simp only [Dot.dot, Function.hPow_apply, id_eq]))
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
        GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h5n θ
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
    classical
    obtain ⟨B, hB⟩ := BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h5n θ (hP0 θ)
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
    have h₁₀ : Tendsto (fun n => γ ^ n * ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖) atTop (𝓝 0) :=
      Eq_0.Lim.of.LtAbs.GtInftySup hγ
        ⟨max B 0, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (h₉ n)⟩
    have h₁₁ : Tendsto (fun n => γ ^ n • ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine h₁₀.congr fun n => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
    have h₁₂ : ∀ t, ‖∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
        Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max Cfd 0) := by
      intro t
      rw [Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₄ θ t (fun y u => Qloc θ t y u)]
      calc
        _ ≤ ∑ y, ‖(M θ).real (s t ⁻¹' {y}) •
            ∑ u, Qloc θ t y u • fderiv ℝ (fun θ' => M.policy.prob θ' y u) θ‖ :=
          norm_sum_le _ _
        _ ≤ ∑ y, (M θ).real (s t ⁻¹' {y}) * (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max Cfd 0)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          refine (norm_sum_le _ _).trans ?_
          refine (Finset.sum_le_sum (g := fun _ => (1 - γ)⁻¹ * |M.env.R| * max Cfd 0) fun u _ => ?_).trans_eq ?_
          ·
            rw [norm_smul]
            exact mul_le_mul (NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t y u)
              ((h8fd θ y u).trans (le_max_left _ _)) (norm_nonneg _) hq
          ·
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = _ := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
    have h₁₃ : Summable (fun t => γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) := by
      have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max Cfd 0))
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
    refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n => ?_) h₁₅
    rw [h₇ n, h₁₄ n]
  exact hfd


/--
Fundamental policy-gradient theorem with action values (gradient / expectation form):
∇ 𝔼[r]((γ ^ id) @ r) = 𝔼[s, a]((γ ^ id) @ fun t ↦ Q(s[t], a[t]) • ∇ log ℙ[M θ](a[t] | s[t])).
The score uses binder sugar `ℙ[M θ](a t | s t)` (option B: scalar `condProb` inside `𝔼`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (hP0 : ∀ θ x, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {x}) ≠ 0)
  (hπ : ∀ θ y u, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable ((Random.Measurable.of.All_Eq.snd.snd h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t))
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      Q θ t (s t) (a t) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) := by
-- proof
  intro hP hsP haP hrP
  have hpol :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        Q θ t (s t) (a t) • ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) := by
    classical
    obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
    obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
    obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
    set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
    set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
    set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
    have hfd :=
      fderiv_tsum_eq_integral_score (M := M) (θ := θ) (γ := γ) (Q := Q) (V := V) (r := r) (s := s) (a := a) h₀ h₁ h₂ h₃ h₄ h₅ hP0 hπ
    let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
    let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
    have hQ : Q = Qloc := funext fun θ => funext fun t => funext fun x => funext fun u =>
      h₂ θ t (fun _ ↦ x) (fun _ ↦ u)
    have hV : V = Vloc := funext fun θ => funext fun t => funext fun x =>
      h₃ θ t (fun _ ↦ x)
    subst hQ hV
    obtain ⟨C, hC⟩ := id h₅
    have h₈ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ C := fun θ x u => by
      simpa [gradient, LinearIsometryEquiv.norm_map] using hC ⟨(θ, x, u), rfl⟩
    let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
    have hEr :=
      Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
        (M := M) h₁ h₄ h₈
    have hsumL : Summable (fun t => γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
      have hs := Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * C * |M.env.R|)
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left ((hEr t).2 θ) (pow_nonneg h₀.1 t)
    have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
    have h₁₂ : ∀ t, ‖∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
        Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0) := by
      intro t
      rw [Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₄ θ t (fun y u => Qloc θ t y u)]
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
              ((h₈ θ y u).trans (le_max_left _ _)) (norm_nonneg _) hq
          ·
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = _ := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
    have hsumR : Summable (fun t => γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) := by
      have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right
        (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0))
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h₁₂ t) (pow_nonneg h₀.1 t)
    have hInt : ∀ t, Integrable (fun ω => Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ) (M θ) := fun t =>
      Random.Integrable_Fun h₁ (M := M) θ t
        (fun y u => Qloc θ t y u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ)
    have hold :
      ∑' t, γ ^ t • ∇[θ] (∫ ω, r t ω ∂(M θ)) =
        ∑' t, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
          ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) := by
      simp only [gradient]
      simp_rw [hL]
      refine Eq.trans ?_ ((congrArg L hfd).trans ?_)
      ·
        have := hsumL
        refine Eq.trans (tsum_congr fun t => (map_smul L (γ ^ t) _).symm) ?_
        rw [← L.map_tsum]
      ·
        have := hsumR
        rw [L.map_tsum]
        refine tsum_congr fun t => ?_
        have := hInt t
        rw [map_smul, ← L.integral_comp_comm]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => map_smul L _ _)
    have hLeft :
      ∇[θ] (∑' t, γ ^ t • ∫ ω, r t ω ∂(M θ)) =
        ∑' t, γ ^ t • ∇[θ] (∫ ω, r t ω ∂(M θ)) := by
      classical
      have hGet :=
        GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h₅ θ
      have hfun :
        (fun θ => ∑' t, γ ^ t • ∫ ω, r t ω ∂(M θ)) =
          fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ) := by
        funext θ; exact tsum_congr fun t => smul_eq_mul _ _
      simp only [gradient]
      simp_rw [hL, hfun, hGet.fderiv]
      have := hsumL
      rw [L.map_tsum]
      exact tsum_congr fun t => map_smul L (γ ^ t) _
    have hold_old :
      ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ)) =
        (γ ^ (id : ℕ → ℕ)) @ fun t ↦
          ∫ ω, Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) := by
      simpa [Dot.dot] using hLeft.trans hold
    have hLfun :
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
      have hL1 : ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ') =
          ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') := by
        simp only [Dot.dot, Function.hPow_apply, id_eq]
      exact hL1.trans (hswap.trans (by simp only [Dot.dot, Function.hPow_apply, id_eq]))
    classical
    obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, ∀ (y : S) (u : A), ‖∇[θ] (Real.log (M.policy.prob θ y u))‖ ≤ Ms := by
      refine ⟨∑ q : S × A, ‖∇[θ] (Real.log (M.policy.prob θ q.1 q.2))‖, fun y u => ?_⟩
      exact Finset.single_le_sum
        (f := fun q : S × A ↦ ‖∇[θ] (Real.log (M.policy.prob θ q.1 q.2))‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ (y, u))
    have hIntG : ∀ t, Integrable (fun ω ↦
        Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) (M θ) := by
      intro t
      simp only [gradient]
      simp_rw [hL]
      apply Integrable.congr
      · exact ContinuousLinearMap.integrable_comp (L : StrongDual ℝ Θ →L[ℝ] Θ) (hInt t)
      · exact Filter.Eventually.of_forall fun ω =>
          map_smul L (Qloc θ t (s t ω) (a t ω)) _
    have hFb : ∀ t, ∀ ω,
        ‖γ ^ t • Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))‖ ≤
          γ ^ t * ((1 - γ)⁻¹ * |M.env.R| * max Ms 0) := by
      intro t ω
      rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
      refine mul_le_mul (NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t (s t ω) (a t ω))
        ((hMs (s t ω) (a t ω)).trans (le_max_left _ _)) (norm_nonneg _) hq
    have hintG : ∀ t, Integrable (fun ω ↦
        γ ^ t • Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) (M θ) :=
      fun t => Integrable.smul (γ ^ t) (hIntG t)
    have hsumG : Summable fun t ↦
        ∫ ω, ‖γ ^ t • Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))‖ ∂(M θ) := by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right ((1 - γ)⁻¹ * |M.env.R| * max Ms 0))
      calc
        _ ≤ ∫ _, γ ^ t * ((1 - γ)⁻¹ * |M.env.R| * max Ms 0) ∂(M θ) :=
          integral_mono_ae (hintG t).norm (integrable_const _) (Filter.Eventually.of_forall (hFb t))
        _ = γ ^ t * ((1 - γ)⁻¹ * |M.env.R| * max Ms 0) := by simp
    have hR :
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) ∂(M θ) =
        (γ ^ (id : ℕ → ℕ)) @ fun t ↦
          ∫ ω, Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
      rw [← integral_tsum_of_summable_integral_norm hintG hsumG]
      exact tsum_congr fun t => integral_smul _ _
    have hLside :
      ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
        ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ)) := by
      simp only [gradient]
      exact congrArg (fun f ↦ (InnerProductSpace.toDual ℝ Θ).symm (fderiv ℝ f θ)) hLfun
    have hint :
      ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
        ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          Qloc θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) ∂(M θ) :=
      hLside.trans (hold_old.trans hR.symm)
    have hE_L :
      (fun θ' ↦ 𝔼[r: M θ']((γ ^ (id : ℕ → ℕ)) @ r)) =
        (fun θ' ↦ ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ')) := by
      funext θ'
      have : PSpace (M θ') (AsPathRV.path (r)) :=
        PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
      exact ExpectDotPow_Id.eq.Integral_ExtDotPow_Id (M := M) (θ := θ') (γ := γ) (r := r)
    have hL :
      ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
        ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) := by
      simp only [gradient]
      exact congrArg (fun f ↦ (InnerProductSpace.toDual ℝ Θ).symm (fderiv ℝ f θ)) hE_L
    have : PSpace (M θ) (AsPathRV.path s) :=
      PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
    have : PSpace (M θ) (AsPathRV.path a) :=
      PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
    refine hL.trans (hint.trans ?_)
    · exact (expect_smul_grad_eq_integral (M := M) (θ := θ) (γ := γ) (Q := Qloc θ) (r := r) (s := s)
        (a := a) h₁).symm
  classical
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) :=
    gradLogProbCond_ae_eq_gradLogPol (M := M) (θ := θ) (r := r) (s := s) (a := a)
      h₁ h₄ h₅ hP
  have hIntPol :
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        Q θ t (s t) (a t) • ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        Q θ t (s t ω) (a t ω) • ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω)))) ∂(M θ) :=
    expect_smul_grad_eq_integral (M := M) (θ := θ) (γ := γ) (Q := Q θ) (r := r) (s := s) (a := a) h₁
  -- Expect ℙ → observation integral (hP in scope for SinglePSpace / option B)
  have hIntP :
    𝔼[s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        Q θ t (s t) (a t) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        Q θ t (s t ω) (a t ω) •
          ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) ∂(M θ) := by
    have : ∀ t, SinglePSpace (M θ) (a t, s t) := hP θ
    rw [Expectation.ofRV, expectation_bochner]
    have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    refine (integral_map hx ?_).trans ?_
    ·
      simp only [Dot.dot, Function.hPow_apply, id_eq]
      refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t => ?_).aestronglyMeasurable
      exact StronglyMeasurable.comp_measurable
        (f := fun q : S × A ↦
          (γ ^ t) • Q θ t q.1 q.2 • ∇[θ] (ℙ[M θ]((a t) = q.2 | (s t) = q.1) : ℝ).log)
        StronglyMeasurable.of_discrete
        (show Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) from
          ((measurable_pi_apply t).comp measurable_fst).prodMk
            ((measurable_pi_apply t).comp measurable_snd))
    ·
      simp only [JointRandomSymbol, AsPathRV.path_process, Dot.dot, Function.hPow_apply, id_eq]
  refine hpol.trans (hIntPol.trans ?_)
  ·
    refine Eq.trans ?_ hIntP.symm
    ·
      refine Eq.symm ?_
      ·
        refine integral_congr_ae ?_
        ·
          have hAll : ∀ᵐ ω ∂(M θ), ∀ t,
            ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
              ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) := by
            rwa [ae_all_iff]
          filter_upwards [hAll] with ω hω
          simp only [Dot.dot, Function.hPow_apply, id_eq]
          exact tsum_congr fun t => by rw [hω t]


-- created on 2023-03-30
-- updated on 2026-10-18 (heartbeat extracts)

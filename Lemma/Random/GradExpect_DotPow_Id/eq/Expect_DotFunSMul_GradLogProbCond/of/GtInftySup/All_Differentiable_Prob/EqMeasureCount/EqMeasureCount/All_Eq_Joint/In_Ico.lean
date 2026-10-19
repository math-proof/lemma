import Lemma.Random.Integral_SMulGetDotFderivLog.eq.Integral_SMulQFderiv.of.All_Eq_Joint.InIco0
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure Set
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 625000


private lemma expect_finset_smul_gradLogProb_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {θ : Θ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
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
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [gradient]
  exact congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd


/-- Path-binder finset Expect of an arbitrary score = observation integral (ℙ-free). -/
private lemma expect_finset_smul_score_eq_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[(γ ^ (id : ℕ → ℕ)) @ (fun t ↦ (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t]))]`.
`h₂`, `h₃`: `θ ↦ π_θ(u | x)` is differentiable with a uniformly bounded gradient
(without them the statement is false). The bound on `∇V` over the reachable pairs
`(t, x)` is not assumed: it follows from time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`). Densities are taken w.r.t. the counting
measures (`hS`, `hA`), so `ℙ[M θ](a[t] = u | s[t] = x)` is the policy `π_θ(u | x)` at reachable states.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) = 𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) := by
-- proof
  intro hP _ _ _
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
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
      GradExpect_DotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
        (θ := θ) h₀ h₁ hS hA hQ_expect hV_expect h₂ h₃o
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
      exact mul_le_mul_of_nonneg_left
        ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
            (M := M) h₁ h₂ hCb t).2 θ)
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
      -- GradExpect RHS is P-score Expect; unwrap then bridge ae to pol for fderiv goal
      have hSP : ∀ θ' t', SinglePSpace (M θ') (a t', s t') := fun θ' t' =>
        SinglePSpace.of.EqMeasureCount.Measurable
          ((Random.Measurable.of.All_Eq.snd.snd h₁ t').prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t'))
          (by
            show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
            rw [hA, hS, Count.eq.ProdCountS])
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
          h₁ hS hA h₂ h₃o hSP t).mono fun _ h => h.symm
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
      BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ
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
    exact (Integral_SMulGetDotFderivLog.eq.Integral_SMulQFderiv.of.All_Eq_Joint.InIco0 (M := M) (θ := θ) h₀ h₁).symm
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃o t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
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
  have hRb := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0 (X := fun _ _ r k => r k)
    h₀ h₁ hS hA (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hA' h₂ h₃o
  refine Eq.trans ?_ ((congrArg L hold).trans hRb)
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ).fderiv, gradient, hL]
  congr 2
  funext θ'
  have hr' : ∀ t, PSpace (M θ') (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have hpr' : PSpace (M θ') (AsPathRV.path (r)) :=
    PSpace_Path.of.All_PSpace hr'
  refine Eq.trans ?_ (hRint θ')
  simp only [Expectation.asRV_process, Dot.dot]
  rw [Expectation.ofRV, expectation_real]
  refine (integral_map hpr'.aemeasurable ?_).trans ?_
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
  · rfl


-- created on 2023-04-07
-- updated on 2026-10-18 (short-path P-pol bridge)

import Lemma.Random.ExpectSMul.eq.ExpectSMulExpectCond.of.All_Eq.In_Ico
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
import sympy.core.function
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob
import Lemma.Random.Integrable.of.In_Ico
import Lemma.Random.V.eq.Integral.of.Measurable
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure Set
set_option maxHeartbeats 625000


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
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
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
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
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
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[(γ ^ (id : ℕ → ℕ)) @ (fun t ↦ (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t]))]`.
`h₂`, `h₃`: `θ ↦ π_θ(u | x)` is differentiable with a uniformly bounded gradient
(without them the statement is false). The bound on `∇V` over the reachable pairs
`(t, x)` is not assumed: it follows from time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`). Densities are taken w.r.t. the counting measures (`CountableMeasure`), so
`ℙ[M θ](a[t] = u | s[t] = x)` is the policy `π_θ(u | x)` at reachable states;
the `SinglePSpace` facts the `ℙ` terms need follow from `CountableMeasure.measure_eq_count`.
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
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ s a, Differentiable ℝ (M.policy.prob · s a))
  (h₃ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) = 𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log) := by
-- proof
  intro hP _ _ _
  classical
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
  have hS : (ReferenceMeasure.measure : Measure S) = Measure.count := CountableMeasure.measure_eq_count
  have hA : (ReferenceMeasure.measure : Measure A) = Measure.count := CountableMeasure.measure_eq_count
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
      GradExpect_DotPow_Id.eq.AddExpect_Sum_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico
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
      have hmeasEq : (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) =
        Measure.count := by
        rw [hA, hS, Count.eq.ProdCountS]
      have hSP : ∀ θ' t', SinglePSpace (M θ') (a t', s t') := fun θ' t' =>
        SinglePSpace.of.EqMeasureCount.Measurable
          ((Random.Measurable.of.All_Eq.snd.snd h₁ t').prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t'))
          hmeasEq
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
        fun _θ => PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ j).aemeasurable⟩)
      rw [Expectation.ofRV, expectation_bochner]
      have hx : AEMeasurable
          (JointRandomSymbol (Expectation.asRV r)
            (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a))) (M θ) :=
        PSpace.aemeasurable
      refine (integral_map hx (hGpath.smul hψpath3).aestronglyMeasurable).trans ?_
      simp only [JointRandomSymbol, AsPathRV.path_process]
      rfl
    have hQ :
        𝔼[s, a : M θ](
            𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t], a[t]) • ψ (s t) (a t)) =
          ∫ ω, Qloc θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
      have : PSpace (M θ) (AsPathRV.path s) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ j).aemeasurable⟩)
      have : PSpace (M θ) (AsPathRV.path a) :=
        PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ j).aemeasurable⟩)
      have : ∀ θ', PSpace (M θ') (AsPathRV.path r) :=
        fun _θ => PSpace_Path.of.All_PSpace
          (fun j => ⟨(Random.Measurable.of.All_Eq.fst h₁ j).aemeasurable⟩)
      rw [Expectation.ofRV, expectation_bochner]
      have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
        PSpace.aemeasurable
      refine (integral_map hx (hQpath.smul hψpath2).aestronglyMeasurable).trans ?_
      simp only [JointRandomSymbol, AsPathRV.path_process]
      change ∫ ω, Qloc θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) =
        ∫ ω, Qloc θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
      rfl
    -- ∫Q = 𝔼[Q] = 𝔼[G] = ∫G
    exact hQ.symm.trans (hlie.symm.trans hG)
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
`A[t] = γ ** Stack[k](k) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])`,
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • A[t] • ∇ log π(a[t] | s[t])]`
(rewards are bounded by the environment, so both series may be taken inside `𝔼`).
Almost surely `A[t] = γ ** Stack[k](k) @ r[t:] - V(s[t])` (telescoping, using `|V| ≤ (1 - γ)⁻¹ |Rmax|`),
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
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ s a, Differentiable ℝ (M.policy.prob · s a))
  (h₃ : sup[θ, s, a] ‖∇[θ] M.policy.prob θ s a‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [CountableMeasure.measure_eq_count, CountableMeasure.measure_eq_count, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V : Θ ⇀ ℕ ⇀ (ℕ ⇀ S) → ℝ := ⟨fun θ => ⟨fun t («s.bvar» : ℕ ⇀ S) =>
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t] = «s.bvar»[t])⟩⟩
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun t δ k => V[θ, t + k] ⟨fun _ => δ k⟩⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ V V_θ
  classical
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
  have hS : (ReferenceMeasure.measure : Measure S) = Measure.count := CountableMeasure.measure_eq_count
  have hA : (ReferenceMeasure.measure : Measure A) = Measure.count := CountableMeasure.measure_eq_count
  let G : (ℕ → ℝ × S × A) → Θ := fun ω => ∑' t, γ ^ t • ((∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)) • ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log)
  have hG : PSpace (M θ) G := ⟨(StronglyMeasurable.tsum fun t => (StronglyMeasurable.smul
      (Measurable.tsum fun k =>
        (((Random.Measurable.of.All_Eq.fst h₁ (t + k)).add (((measurable_of_countable (fun x : S => V θ (t + k + 1) ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k + 1))).const_mul γ)).sub
          ((measurable_of_countable (fun x : S => V θ (t + k) ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (t + k)))).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        ∇[θ] (ℙ[M θ]((a t) = p.2 | (s t) = p.1) : ℝ).log)).comp_measurable
          ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)))).const_smul (γ ^ t)).aestronglyMeasurable.aemeasurable⟩
  have hPs : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable (Random.Measurable.of.All_Eq.snd.fst h₁ t) hS
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hVbd : ∀ t x, |Vloc θ t x| ≤ (1 - γ)⁻¹ * |M.env.R| := fun t x => by
    simpa only [Real.norm_eq_abs] using NormV.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t x
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ t x, |Vloc θ t x| ≤ B := ⟨_, hVbd⟩
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) → (V θ' t ⟨fun _ => x⟩ = Vloc θ' t x) := fun θ' t x _ =>
    rfl
  have key : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ -
        V θ (t + k) ⟨fun _ => s (t + k) ω⟩)) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
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
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ -
        V θ (t + k) ⟨fun _ => s (t + k) ω⟩)) •
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
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩ - V θ (t + k) ⟨fun _ => s (t + k) ω⟩)‖ ≤
        (1 - γ)⁻¹ * (|M.env.R| + γ * B + B) := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ, AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hr hR t
    have hb : ∀ n, |V θ n ⟨fun _ => s n ω⟩| ≤ B := fun n => by
      rw [hVr θ n _ (hR n)]
      exact hBd n _
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 k)
    calc
      _ ≤ ‖r (t + k) ω‖ + ‖γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1) ω⟩‖ + ‖V θ (t + k) ⟨fun _ => s (t + k) ω⟩‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |M.env.R| + γ * B + B := by
        rw [norm_mul, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs, Real.norm_eq_abs]
        exact add_le_add (add_le_add (hr _) (mul_le_mul_of_nonneg_left (hb _) h₀.1)) (hb _)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  have hT : ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k))) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) :=
    main h₀ h₁ h₂ h₃
  have hRae : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  have hRb := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0 (X := fun _ _ r k => r k)
    h₀ h₁ hS hA (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hRae h₂ h₃
  refine hT.trans (hRb.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm holdRA).trans ?_))
  have hAdvExp :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
      (X := fun s _ r k => r k + γ * V θ (k + 1) ⟨fun _ => s (k + 1)⟩ - V θ k ⟨fun _ => s k⟩)
      h₀ h₁ hS hA
      (fun k => ((Random.Measurable.of.All_Eq.fst h₁ k).add (((measurable_of_countable (fun x : S => V θ (k + 1) ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ (k + 1))).const_mul γ)).sub
        ((measurable_of_countable (fun x : S => V θ k ⟨fun _ => x⟩)).comp (Random.Measurable.of.All_Eq.snd.fst h₁ k)))
      hAdv h₂ h₃
  refine hAdvExp.trans ?_
  -- V_θ[t] s[t:] k = V θ (t + k) ⟨fun _ => s (t + k)⟩
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
  change
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (fun k => r (t + k) + γ * V θ (t + k + 1) ⟨fun _ => s (t + k + 1)⟩ -
          V θ (t + k) ⟨fun _ => s (t + k)⟩)) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log)) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
          ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log))
  refine congrArg
    (Expectation.ofRV (M θ)
      (JointRandomSymbol (Expectation.asRV r)
        (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a)))) ?_
  funext integ
  dsimp
  congr 1
  funext t
  congr 1
  exact congrArg (fun δ => Dot.dot (γ ^ (id : ℕ → ℕ)) δ)
    (hδθ (fun j => integ.2.1 j) (fun j => integ.1 j) t)


-- created on 2023-04-07
-- updated on 2026-10-20

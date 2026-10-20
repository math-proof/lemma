import Lemma.Random.Zero.eq.AddSum_SMulPowSum_SMul_SMulPow_Sum_SMul.of.Real.ne.Zero.GtInftySup.All_Differentiable.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
import Mathlib.Analysis.Calculus.Gradient.Basic
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob
import Lemma.Random.TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integrable_Fun
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id
import Lemma.Random.PSpace_Path.of.All_PSpace
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Topology Filter Random Set Measure
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 937500


/-- Path-binder form of the finite-horizon Q-score integral. -/
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

/-- Path-binder form of the V-gradient integral. -/
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


/-- Ae equality of score: binder-equality ℙ-log-grad vs `M.policy.prob` log-grad. -/
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


/-- Core fderiv identity: dotted path reward fderiv = finset Q-score integral + terminal V fderiv. -/
private lemma fderiv_dotPow_eq_integral_finset_smul_add
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S] [DecidableEq S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq A]
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {n : ℕ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (hQ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      Q θ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (hV : ∀ θ t («s.bvar» : ℕ → S),
      V θ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞) :
  (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) =
    ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Q θ t (s t ω) (a t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
        γ ^ n • ∫ ω, fderiv ℝ (fun θ' => V θ' n (s n ω)) θ ∂(M θ) := by
  classical
  have h₈ : ∀ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ =
    M.env.init.real {x} • (∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
          ∑ u, Q θ t y u • fderiv ℝ (fun θ => M.policy.prob θ y u) θ +
        γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => V θ n y) θ) := by
    intro x
    if hx : M.env.init.real {x} = 0 then
      rw [hx, zero_smul, zero_smul]
    else
      have hP : (M θ).real (s 0 ⁻¹' {x}) ≠ 0 := by rwa [RealPreimageS0.eq.Real h₁]
      have hg := Zero.eq.AddSum_SMulPowSum_SMul_SMulPow_Sum_SMul.of.Real.ne.Zero.GtInftySup.All_Differentiable.All_Eq_ExpectCondDot.All_Eq_ExpectCondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0 (Q := Q) (V := V) h₀ h₁ hS hA hQ hV h₄ h₅ hP n
      have h' : ∀ t y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
        have h'' := RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage (M := M) θ 0 t x y h₁ hP
        rwa [zero_add] at h''
      simp_rw [h'] at hg
      have h : fderiv ℝ (fun θ => V θ 0 x) θ =
        ∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
              ∑ u, Q θ t y u • fderiv ℝ (fun θ => M.policy.prob θ y u) θ +
            γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => V θ n y) θ := by
        apply (InnerProductSpace.toDual ℝ Θ).symm.injective
        simpa [gradient, map_add, map_smul, _root_.map_sum] using hg
      -- Fderiv_V equates fderiv of the *inline* cond-expect Vθ with fderiv Vc;
      -- abstract V matches that inline form only via hV (not definitionally).
      have hVcV : fderiv ℝ (fun θ => M.Vc θ γ x) θ =
          fderiv ℝ (fun θ => V θ 0 x) θ := by
        rw [← Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
            (M := M) 0 x θ h₀ h₁ h₄ h₅ hP]
        congr 1
        funext θ'
        exact (hV θ' 0 (fun _ => x)).symm
      rw [hVcV, h]
  have h₉ : ∀ t, ∫ ω, (γ ^ t * Q θ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑ y, (M θ).real (s t ⁻¹' {y}) •
        ∑ u, (γ ^ t * Q θ t y u) • fderiv ℝ (fun θ' => M.policy.prob θ' y u) θ :=
    fun t => Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₄ θ t (fun y u => γ ^ t * Q θ t y u)
  have h₁₀ : ∫ ω, fderiv ℝ (fun θ' => V θ' n (s n ω)) θ ∂(M θ) =
    ∑ y, (M θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => V θ' n y) θ :=
    Integral.eq.Sum_SMul h₁ (M := M) θ n (fun y => fderiv ℝ (fun θ' => V θ' n y) θ)
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  rw [TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h₅ θ, Finset.sum_congr rfl fun x _ => h₈ x,
    integral_finsetSum _ fun t _ => Random.Integrable_Fun h₁ (M := M) θ t
      (fun y u => (γ ^ t * Q θ t y u) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ)]
  simp_rw [h₉, h₁₀, RealPreimageS.eq.Sum_MulRealPn (M := M) h₁ θ]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    Finset.sum_mul]
  congr 1
  ·
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  ·
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring

/-- Swap: ∫ (γ^id @ r) = (γ^id) @ (∫ r t). -/
private lemma integral_extDotPow_eq_dotPow_integral
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
  (fun θ' ↦ ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ')) =
    fun θ' ↦ (γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ') := by
  funext θ'
  have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
    (All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ').mono fun ω h => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
  have hri : ∀ t, Integrable (fun ω ↦ γ ^ t * r t ω) (M θ') := fun t =>
    Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
  calc
    _ = ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]
    _ = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
      rw [← integral_tsum_of_summable_integral_norm hri]
      · exact tsum_congr fun t => integral_const_mul _ _
      ·
        refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
          ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
        apply le_trans
        · exact integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        · simp
    _ = (γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ') := by
      simp only [Dot.dot, Function.hPow_apply, id_eq]

/-- Path-binder finset Expect of an arbitrary score = observation integral.
ℙ-free: callers elaborate binder/equality ℙ in a `SinglePSpace` context, then pass `score`. -/
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
Finite-horizon policy gradient: for every `n`,
`∇[θ] 𝔼[r]((γ ^ (id : ℕ → ℕ)) @ r) =
  𝔼[s, a](∑ t < n, γ ^ t * Q(s[t], a[t]) • ∇[θ] (log ℙ[M θ](a[t] | s[t]))) +
    γ ^ n • 𝔼[s](∇[θ] (V(s[n])))`.
The score uses binder sugar `ℙ[M θ](a t | s t)` (option B: scalar `condProb` inside `𝔼`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (n : ℕ) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable
      ((Random.Measurable.of.All_Eq.snd.snd h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t))
      (by
        show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
        rw [hA, hS, Count.eq.ProdCountS])
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[s, a : M θ](∑ t ∈ Finset.range n,
        (γ ^ t * Q θ t (s t) (a t)) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) +
      γ ^ n • 𝔼[s : M θ](∇[θ] (V θ n (s n))) := by
-- proof
  intro hP hsP haP hrP
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₄n := h₅
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₅
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
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      Qloc θ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) :=
    fun _ _ _ _ => rfl
  have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
      Vloc θ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) :=
    fun _ _ _ => rfl
  have hfd :
    (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) =
      ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
          γ ^ n • ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ) :=
    fderiv_dotPow_eq_integral_finset_smul_add (M := M) (θ := θ) (γ := γ) (n := n)
      (Q := Qloc) (V := Vloc) (r := r) (s := s) (a := a)
      h₀ h₁ hS hA hQ_expect hV_expect h₄ h₄n
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  obtain ⟨Cp, hCp⟩ := id h₄n
  have hCfd : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hsumL : Summable fun t ↦ γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ := by
    have hs := Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * Cp * |M.env.R|)
    refine Summable.of_norm_bounded hs fun t => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    apply mul_le_mul_of_nonneg_left
      ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
          (M := M) h₁ h₄ hCfd t).2 θ)
      (pow_nonneg h₀.1 t)
  have hInt : Integrable
    (fun ω ↦ ∑ t ∈ Finset.range n,
      (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)
    (M θ) :=
    integrable_finsetSum _ fun t _ =>
      Random.Integrable_Fun h₁ (M := M) θ t
        (fun y u => (γ ^ t * Qloc θ t y u) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ)
  have hIntV : Integrable (fun ω ↦ fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ) (M θ) :=
    Random.Integrable_Fun h₁ (M := M) θ n (fun y _ => fderiv ℝ (fun θ' => Vloc θ' n y) θ)
  have hold :
    (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∇[θ] (∫ ω, r t ω ∂(M θ))) =
      ∫ ω, ∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
              ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) +
          γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq] at hfd
    simp only [Dot.dot, Function.hPow_apply, id_eq, gradient]
    simp_rw [hL]
    refine Eq.trans ?_ ((congrArg L hfd).trans ?_)
    ·
      have := hsumL
      refine Eq.trans (tsum_congr fun t => (map_smul L (γ ^ t) _).symm) ?_
      rw [← L.map_tsum]
    ·
      rw [map_add, map_smul]
      congr 1
      ·
        have := hInt
        rw [← L.integral_comp_comm]
        congr 1
        refine funext fun ω => ?_
        rw [_root_.map_sum]
        refine Finset.sum_congr rfl fun t _ => map_smul L _ _
      ·
        have := hIntV
        rw [← L.integral_comp_comm]
  have hLeft :
    ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∫ ω, r t ω ∂(M θ))) =
      (γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∇[θ] (∫ ω, r t ω ∂(M θ))) := by
    classical
    have hGet :=
      GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h₄n θ
    have hfun :
      (fun θ => ∑' t, γ ^ t • ∫ ω, r t ω ∂(M θ)) =
        fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ) := by
      funext θ; exact tsum_congr fun t => smul_eq_mul _ _
    have hcore :
      ∇[θ] (∑' t, γ ^ t • ∫ ω, r t ω ∂(M θ)) =
        ∑' t, γ ^ t • ∇[θ] (∫ ω, r t ω ∂(M θ)) := by
      simp only [gradient]
      simp_rw [hL, hfun, hGet.fderiv]
      have := hsumL
      rw [L.map_tsum]
      exact tsum_congr fun t => map_smul L (γ ^ t) _
    simpa [Dot.dot, Function.hPow_apply, id_eq] using hcore
  have hold_old :
    ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ (fun t ↦ ∫ ω, r t ω ∂(M θ))) =
      ∫ ω, ∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
              ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) +
          γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
    hLeft.trans hold
  have hLfun :
    (fun θ' ↦ ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ')) =
      fun θ' ↦ (γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ') :=
    integral_extDotPow_eq_dotPow_integral (M := M) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁
  have hLside :
    ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
      ∇[θ] ((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ∫ ω, r t ω ∂(M θ)) := by
    simp only [gradient]
    exact congrArg (fun f ↦ (InnerProductSpace.toDual ℝ Θ).symm (fderiv ℝ f θ)) hLfun
  have hold_pol :
    ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
      ∫ ω, ∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
              ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) +
          γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
    hLside.trans hold_old
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log =
        ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) :=
    gradLogProbCond_ae_eq_gradLogPol (M := M) (θ := θ) (r := r) (s := s) (a := a)
      h₁ hS hA h₄ h₄n hP
  have hRHSpol :
    ∫ ω, ∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
            ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) +
        γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) =
      ∫ ω, ∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
            ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) +
        γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) := by
    have : ∀ t, SinglePSpace (M θ) (a t, s t) := hP θ
    refine congrArg₂ (· + ·) ?_ rfl
    exact integral_finset_smul_score_eq_of_ae (M := M) (θ := θ) (γ := γ) (n := n)
      (Q := Qloc θ) (s := s) (a := a)
      (score₁ := fun t x u => ∇[θ] (Real.log (M.policy.prob θ x u)))
      (score₂ := fun t x u => ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log)
      (fun t => (hscore t).mono fun ω h => h.symm)
  have hold_int :
    ∇[θ] (∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r) ω ∂(M θ)) =
      ∫ ω, ∑ t ∈ Finset.range n,
            (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
              ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) +
          γ ^ n • ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
    hold_pol.trans hRHSpol
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
  have : PSpace (M θ) (AsPathRV.path s) := hsP
  have : PSpace (M θ) (AsPathRV.path a) := haP
  have hRVθ :
    𝔼[s : M θ](∇[θ] (Vloc θ n (s n))) =
      ∫ ω, ∇[θ] (Vloc θ n (s n ω)) ∂(M θ) :=
    expect_gradV_eq_integral (M := M) (θ := θ) (n := n) (V := fun θ' => Vloc θ' n) (s := s)
  have hRQpol :
    𝔼[s, a : M θ](∑ t ∈ Finset.range n,
        (γ ^ t * Qloc θ t (s t) (a t)) •
          ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) =
      ∫ ω, ∑ t ∈ Finset.range n,
        (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
          ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) :=
    expect_finset_smul_gradLogProb_eq_integral (M := M) (θ := θ) (γ := γ) (n := n)
      (Q := Qloc θ) (r := r) (s := s) (a := a) h₁
  have hRQP :
    𝔼[s, a : M θ](∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t) (a t)) •
            ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) =
        ∫ ω, ∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
            ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) := by
    have : ∀ t, SinglePSpace (M θ) (a t, s t) := hP θ
    -- ℙ elaborated here (SinglePSpace in scope); lemma itself is ℙ-free.
    exact expect_finset_smul_score_eq_integral (M := M) (θ := θ) (γ := γ) (n := n)
      (Q := Qloc θ)
      (score := fun t x u => ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log)
      (s := s) (a := a)
  -- Bridge pol Expect → ℙ Expect (extracted helpers)
  have hInt_pol_eq_P :
    ∫ ω, ∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
            ∇[θ] (Real.log (M.policy.prob θ (s t ω) (a t ω))) ∂(M θ) =
      ∫ ω, ∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
            ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log ∂(M θ) := by
    have : ∀ t, SinglePSpace (M θ) (a t, s t) := hP θ
    exact integral_finset_smul_score_eq_of_ae (M := M) (θ := θ) (γ := γ) (n := n)
      (Q := Qloc θ) (s := s) (a := a)
      (score₁ := fun t x u => ∇[θ] (Real.log (M.policy.prob θ x u)))
      (score₂ := fun t x u => ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ).log)
      (fun t => (hscore t).mono fun ω h => h.symm)
  have hExpect_pol_eq_P :
    𝔼[s, a : M θ](∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t) (a t)) •
            ∇[θ] (Real.log (M.policy.prob θ (s t) (a t)))) =
      𝔼[s, a : M θ](∑ t ∈ Finset.range n,
          (γ ^ t * Qloc θ t (s t) (a t)) •
            ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) :=
    hRQpol.trans (hInt_pol_eq_P.trans hRQP.symm)
  refine hE_L.trans (hold_pol.trans ?_)
  ·
    refine (congrArg₂ (· + ·) hRQpol.symm (congrArg (γ ^ n • ·) hRVθ.symm)).trans ?_
    ·
      exact congrArg₂ (· + ·) hExpect_pol_eq_P rfl


-- created on 2023-04-04
-- updated on 2026-10-18 (pol↔ℙ extracts)

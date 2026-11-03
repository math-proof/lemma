import Lemma.Random.EqFderiv_FunVc_AddSum_SMulSMulSum_SMul.of.In_Ico.GtInftySup_Norm.All_AllDifferentiable_FunPolProb
import Lemma.Random.Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Differentiable_FunVc.of.InIco0.GtInftySup_Norm.All_All_Differentiable_FunPolProb
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Filter


private lemma Q_eq_Qk
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (M : Model Θ S A)
  (θ : Θ)
  {γ : ℝ}
  (hγ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (u : A)
  (hP : (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u ≠ 0) :
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  Q θ t x u = M.Qk θ γ x u := by
  intro Qθ
  have := M.env.trans_markov
  have hQ :=
    Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
      (M := M) θ t x u hγ h₁ hP
  have hsum :
      (∑ y : S, (M.env.trans (x, u)).real {y} *
        ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)) =
      (∑ y : S, (M.env.trans (x, u)).real {y} * M.V0 θ γ y) := by
    refine Finset.sum_congr rfl fun (y : S) _ => ?_
    by_cases hy : (M.env.trans (x, u)).real {y} = 0
    · simp [hy]
    · rw [Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) hγ θ y]
  have hT : ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u)) =
      ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ γ y := by
    rw [integral_fintype Integrable.of_finite]
    simp [smul_eq_mul, mul_comm]
  calc
    Qθ θ t x u
        = (∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
            γ * ∑ y, (M.env.trans (x, u)).real {y} *
              ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
                ∂(M.stageK θ y) := hQ
    _ = (∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u))) +
            γ * ∑ y, (M.env.trans (x, u)).real {y} * M.V0 θ γ y := by
          refine congrArg (fun z : ℝ =>
              (∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u))) + γ * z) hsum
    _ = M.rk x u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans (x, u)) := by
          simp only [Model.rk]
          rw [← hT]
    _ = M.Qk θ γ x u := rfl

/--
policy-gradient recursion for the model value functions on a reachable state
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  let V (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  fderiv ℝ (fun θ' => V θ' t x) θ =
    ∑ u, Q θ t x u • fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ +
    γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ' => V θ' (t + 1) y) θ := by
-- proof
  intro Qθ Vθ
  have hr : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  have hs : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  -- local V =ᶠ V0 near θ on the reachable state x at time t
  have hEV : (fun θ' => Vθ θ' t x) =ᶠ[𝓝 θ] fun θ' => M.V0 θ' γ x := by
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {x})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ t x θ).continuousAt
    filter_upwards [hc.eventually_ne h₄] with θ' ht
    have hseries :
        Vθ θ' t x =
          ∑' k, γ ^ k * ∫ z, M.Kf θ' (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ' x) :=
      V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) (r := r) (s := s) (a := a)
        θ' t x h₀ h₁ ht
    exact hseries.trans
      (Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ' x).symm
  rw [EventuallyEq.fderiv_eq hEV,
    EqFderiv_FunVc_AddSum_SMulSMulSum_SMul.of.In_Ico.GtInftySup_Norm.All_AllDifferentiable_FunPolProb
      (M := M) h₂ h₃ h₀ x θ]
  congr 1
  ·
    refine Finset.sum_congr rfl fun u _ => ?_
    if hu : M.policy.prob θ x u = 0 then
      rw [Fderiv_FunProbPol.eq.Zero.of.ProbPolEq0 (M := M) θ x u hu, smul_zero, smul_zero]
    else
      have hQ : Qθ θ t x u = M.Qk θ γ x u :=
        Q_eq_Qk h₁ M θ h₀ t x u (mul_ne_zero h₄ hu)
      rw [← hQ]
  ·
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    if hy : M.P1 θ x y = 0 then
      rw [hy, zero_smul, zero_smul]
    else
      obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      have hy_t :
          (M θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 :=
        RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage
          (M := M) θ t x u y h₁ h₄ hu
      have hEV' : (fun θ' => Vθ θ' (t + 1) y) =ᶠ[𝓝 θ] fun θ' => M.V0 θ' γ y := by
        have hc : ContinuousAt (fun θ' => (M θ').real (s (t + 1) ⁻¹' {y})) θ :=
          (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
            (M := M) h₁ h₂ h₃ (t + 1) y θ).continuousAt
        filter_upwards [hc.eventually_ne hy_t] with θ' ht
        have hseries :
            Vθ θ' (t + 1) y =
              ∑' k, γ ^ k * ∫ z, M.Kf θ' (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z
                ∂(M.stageK θ' y) :=
          V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) (r := r) (s := s) (a := a)
            θ' (t + 1) y h₀ h₁ ht
        exact hseries.trans
          (Vc.eq.TSum_MulPowIntegral.of.Ne0Real_Preimage.In_Ico (M := M) h₀ θ' y).symm
      rw [EventuallyEq.fderiv_eq hEV']


-- created on 2026-10-06
-- updated on 2026-11-03

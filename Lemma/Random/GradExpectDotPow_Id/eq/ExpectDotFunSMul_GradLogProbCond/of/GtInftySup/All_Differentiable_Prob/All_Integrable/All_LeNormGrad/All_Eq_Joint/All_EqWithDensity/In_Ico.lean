import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Theorem.Function
import Theorem.Dynamics.PolicyTrajectory.ContinuousAction.Part3
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
import Lemma.Random.TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul_Qkd.eq.Integral_SMul_SubAddVkd.of.In_Ico.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul.of.In_Ico.In_Ico.All_EqWithDensity
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.AeAll_LeNorm_TSum_MulPowSubAddRMul_VkdVkdMulSub1DeltaBound.of.In_Ico.In_Ico.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
set_option maxHeartbeats 900000


/--
Unbiased continuous-action advantage estimate: with
`V_θ[t] δ k := M.Vkd θ γ (δ k)` and density score `∇ log π`,
`∇𝔼[(γ ^ id) @ r] = 𝔼[(γ ^ id) @ fun t ↦ ((γ ^ id) @ (r[t:] + γ • V_θ[t+1] s[t+1:] - V_θ[t] s[t:])) • ∇ log π]`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _t δ k => M.Vkd θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
-- proof
  intro _ _ _ _ V_θ
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
  have hr : ∀ θ' t, PSpace (M θ') (r t) := fun _ t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun θ' =>
    PSpace_Path.of.All_PSpace (hr θ')
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  have hφg : StronglyMeasurable
      (fun z : S × A => gradient (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    simp only [gradient]
    exact ((InnerProductSpace.toDual ℝ Θ).symm.continuous.comp_stronglyMeasurable hφ)
  have hMsg : ∀ y u,
      ‖gradient (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMs y u
  set ψ : S → A → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ
  -- discounted return series swap
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable
        _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc
        _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
          integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hGet :=
    GetTSum_SMul.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
      (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
  have hEfun :
      (fun θ' ↦ 𝔼[r: M θ']((γ ^ (id : ℕ → ℕ)) @ r)) =
        (fun θ' ↦ ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ')) := by
    funext θ'
    have : PSpace (M θ') (AsPathRV.path r) :=
      PSpace_Path.of.All_PSpace (hr θ')
    refine (ExpectDotPow_Id.eq.Integral_ExtDotPow_Id.of.All_EqWithDensity
      (M := M) (θ := θ') (γ := γ) (r := r)).trans ?_
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    exact hRint θ'
  have hLHS :
      ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
        L (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
    simp only [gradient, hL]
    exact congrArg (fun f ↦ L (fderiv ℝ f θ)) hEfun ▸
      congrArg L hGet.fderiv.symm ▸ rfl
  -- ∑ γ^t • fderiv(∫r) = ∑ γ^t • ∫ (∑ γ^k δ) • fderiv log
  have hchain :
      ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
        ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
          M.Vkd θ γ (s (t + k) ω))) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    have hTSum :=
      TSum_SMul.eq.Integral_Fderiv_Vkd.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ θ
    have hQ :=
      Integral_Fderiv_Vkd.eq.TSum_SMul_Integral_SMul_Qkd_FderivLog.of.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.All_Measurable_Prob.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs
    refine hTSum.trans (hQ.trans (tsum_congr fun t => congrArg (fun z => γ ^ t • z) ?_))
    have hQδ :=
      Integral_SMul_Qkd.eq.Integral_SMul_SubAddVkd.of.In_Ico.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ hφ hMs t
    have hgae :=
      Integral_SMul.of.In_Ico.In_Ico.All_EqWithDensity
        (M := M) h₀ h₁ hπ θ h₀ t ψ hψ ⟨Ms, hMs⟩
    exact hQδ.trans hgae.symm
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
      (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) =>
          r k + γ * M.Vkd θ γ (s (k + 1)) - M.Vkd θ γ (s k))
        (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst h₁ k).add
      (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
          (Random.Measurable.of.All_Eq.snd.fst h₁ (k + 1))).const_mul γ)).sub
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst h₁ k))
  have hbd :=
    AeAll_LeNorm_TSum_MulPowSubAddRMul_VkdVkdMulSub1DeltaBound.of.In_Ico.In_Ico.All_EqWithDensity
      (M := M) h₀ h₁ h₀ θ
  set Bδ : ℝ := (1 - γ)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|)
  have hAdvExp :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity
      (M := M) (θ := θ) (γ := γ)
      (X := fun s _ r k => r k + γ * M.Vkd θ γ (s (k + 1)) - M.Vkd θ γ (s k))
      (B := Bδ) (Ms := Ms) h₀ h₁ hmeas hbd hφg hMsg
  refine hLHS.trans ((congrArg L hchain).trans (hAdvExp.trans ?_))
  -- rewrite ∑' sugar into Dot / V_θ form
  refine congrArg
    (Expectation.ofRV (M θ)
      (JointRandomSymbol (Expectation.asRV r)
        (JointRandomSymbol (Expectation.asRV s) (Expectation.asRV a)))) ?_
  funext integ
  -- LHS: ∑' γ^t • (((γ^k)@δ) • ∇log); RHS: (γ^id) @ fun t ↦ (((γ^id)@δ_Vθ) • ∇log)
  change
      (∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @
              (fun k => integ.1 (t + k) + γ * M.Vkd θ γ (integ.2.1 (t + k + 1)) -
                M.Vkd θ γ (integ.2.1 (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t)))) =
        ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
          (((γ ^ (id : ℕ → ℕ)) @
              ((fun k => integ.1 (t + k)) +
                γ • (fun k => V_θ[t + 1] (fun j => integ.2.1 (t + 1 + j)) k) -
                fun k => V_θ[t] (fun j => integ.2.1 (t + j)) k)) •
            ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t))))
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  refine tsum_congr fun t => ?_
  congr 1
  congr 1
  refine tsum_congr fun k => ?_
  have hk : t + k + 1 = t + 1 + k := by omega
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_θ, hk]


-- created on 2026-10-20

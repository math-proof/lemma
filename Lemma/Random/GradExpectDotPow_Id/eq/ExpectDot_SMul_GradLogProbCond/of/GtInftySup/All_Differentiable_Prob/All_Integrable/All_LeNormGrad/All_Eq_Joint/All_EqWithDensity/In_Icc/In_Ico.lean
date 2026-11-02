import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Theorem.Data.List.List
open MeasureTheory PolicyGradient Filter Random
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 900000


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438) for continuous actions:
with `V_θ[t] δ k := M.Vkd θ γ (δ k)`, `ℓ ∈ [0, 1]`, and score `∇ log ℙ(a[t] | s[t])`,
`∇𝔼[(γ ^ id) @ r] = 𝔼[(γ ^ id) @ fun t ↦ (((γ * ℓ) ^ id) @ (r[t:] + γ • V_θ[t+1] s[t+1:] - V_θ[t] s[t:])) • ∇ log π]`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ ℓ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (htr : DensityModel.IsPolicyTrajectory M r s a)
  (haj : DensityModel.AbsContJointAS M a s)
  (hfactor : ∀ θ t («\sf{s}» : ℕ ⇀ S) («\sf{a}» : ℕ ⇀ A),
    M.policy.prob θ «\sf{s}»[t] «\sf{a}»[t] =
      (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)))
  (hMs : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms) :
-- imply
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → S) → ℕ → ℝ := ⟨fun _ δ k => M.Vkd θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  intro _ _ _ _ V_θ
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (htr.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (htr.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (htr.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let : MeasurableSpace Θ := borel Θ
  let : BorelSpace Θ := ⟨rfl⟩
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd htr.stage_eq t).aemeasurable⟩)
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₁.1, (mul_le_of_le_one_right h₀.1 h₁.2).trans_lt h₀.2⟩
  -- parent / Integral_SMul still take the dual (`fderiv`) form of the score
  have h₃' : ∀ θ' x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ'‖ ≤ g x u :=
    fun θ' x u => by simpa [gradient, LinearIsometryEquiv.norm_map] using h₃ θ' x u
  have hφ' : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    simpa [gradient] using
      (InnerProductSpace.toDual ℝ Θ).continuous.comp_stronglyMeasurable hφ
  have hMs' : ∀ y u,
    ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMs y u
  set ψ : S → A → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ'
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
    (fun (s : ℕ → S) (_ : ℕ → A) (r : ℕ → ℝ) (k : ℕ) =>
        r k + γ * M.Vkd θ γ (s (k + 1)) - M.Vkd θ γ (s k))
      (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst htr.stage_eq k).add
      (((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
          (Random.Measurable.of.All_Eq.snd.fst htr.stage_eq (k + 1))).const_mul γ)).sub
      ((Measurable_Vkd.of.All_Measurable_Prob (M := M) hπ θ γ).comp
        (Random.Measurable.of.All_Eq.snd.fst htr.stage_eq k))
  have hbd : ∀ c ∈ Set.Ico (0 : ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
    ‖∑' k, c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
      M.Vkd θ γ (s (t + k) ω))‖ ≤
      (1 - c)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|) := fun c hc' =>
    AeAll_LeNorm_TSum_MulPowSubAddRMul_VkdVkdMulSub1DeltaBound.of.In_Ico.In_Ico.All_EqWithDensity
      (M := M) h₀ htr.stage_eq hc' θ
  -- `c`-discounted advantage against the density score collapses to the first residual
  have hinner : ∀ c ∈ Set.Ico (0 : ℝ) 1, ∀ t, ∫ ω,
    (∑' k, c ^ k * (r (t + k) ω + γ * M.Vkd θ γ (s (t + k + 1) ω) -
      M.Vkd θ γ (s (t + k) ω))) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
    ∫ ω, (r t ω + γ * M.Vkd θ γ (s (t + 1) ω) - M.Vkd θ γ (s t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
    fun c hc' t =>
      Integral_SMul.of.In_Ico.In_Ico.All_EqWithDensity
        (M := M) h₀ htr.stage_eq hπ θ hc' t ψ hψ ⟨Ms, hMs'⟩
  have hbase :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
      (M := M) h₀ htr.stage_eq hπ h₂ h₃' h₄ h₅ hφ' hMs'
  -- rewrite V_θ sugar into Vkd pointwise form for dual conversion
  have hbaseexp :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @
            (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine hbase.trans ?_
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine tsum_congr fun t => ?_
    congr 1
    congr 1
    refine tsum_congr fun k => ?_
    have hk : t + 1 + k = t + k + 1 := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_θ,
      Function.getSliceFrom_apply, hk]
  -- Dot sugar ↔ path tsum sugar
  have hDotγ :
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @
            (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
      𝔼[r, s, a : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @
              (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
  have hDotc :
    𝔼[r, s, a : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => (γ * ℓ) ^ k) @
              (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) @
            (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
  set Bγ : ℝ := (1 - γ)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|)
  set Bc : ℝ := (1 - γ * ℓ)⁻¹ * ((3 / (1 - γ) - 1) * |M.env.R|)
  have hA₁ :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
      (M := M) (θ := θ) (γ := γ) (c := γ)
      (X := fun s _ r k => r k + γ * M.Vkd θ γ (s (k + 1)) - M.Vkd θ γ (s k))
      (B := Bγ) (Ms := Ms) h₀ htr.stage_eq hmeas (hbd γ h₀) hφ hMs
  have hA₂ :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
      (M := M) (θ := θ) (γ := γ) (c := γ * ℓ)
      (X := fun s _ r k => r k + γ * M.Vkd θ γ (s (k + 1)) - M.Vkd θ γ (s k))
      (B := Bc) (Ms := Ms) h₀ htr.stage_eq hmeas (hbd (γ * ℓ) hc) hφ hMs
  have hsplit :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) @
            (fun k => r (t + k) + γ * M.Vkd θ γ (s (t + k + 1)) - M.Vkd θ γ (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) :=
    hbaseexp.trans (hDotγ.trans (hA₁.symm.trans
      ((congrArg (InnerProductSpace.toDual ℝ Θ).symm
          (tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t])).trans
        (hA₂.trans hDotc))))
  have hPol :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) @ (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:])) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine hsplit.trans ?_
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine tsum_congr fun t => ?_
    congr 1
    congr 1
    refine tsum_congr fun k => ?_
    have hk : t + k + 1 = t + 1 + k := by omega
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_θ,
      Function.getSliceFrom_apply, hk]
  refine hPol.trans ?_
  refine congrArg
    (Expectation.ofRV (M θ)
      (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
  funext integ
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  refine tsum_congr fun t => ?_
  have hsc :=
    congrArg (fun φ : Θ → ℝ => gradient φ θ)
      (funext fun θ' => congrArg Real.log (hfactor θ' t ⟨integ.2.1⟩ ⟨integ.2.2⟩))
  rw [hsc]
  congr 1


-- created on 2026-10-20
-- updated on 2026-11-02

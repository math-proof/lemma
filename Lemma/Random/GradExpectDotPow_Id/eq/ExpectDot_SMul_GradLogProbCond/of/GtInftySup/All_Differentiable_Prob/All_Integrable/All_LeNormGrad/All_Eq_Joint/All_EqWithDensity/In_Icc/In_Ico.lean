import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
import Lemma.Random.MEq_Clip.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormClip.le.Abs_R
import Theorem.Probability.CondExpectation
import Theorem.Function
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Theorem.Data.List.List
open MeasureTheory ProbabilityTheory PolicyGradient Filter Random Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 900000


private lemma ae_norm_residual
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜} {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {V : ℕ ⇀ 𝒮 → ℝ}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (hV : ∀ (k : ℕ) (x : 𝒮),
    V[k] x =
      Expectation.condEval (M θ) (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => fun i => r i ω) (s k)
        (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) x) :
  ∀ᵐ ω ∂(M θ), ∀ j,
    ‖r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)‖ ≤
      (2 / (1 - γ)) * |M.env.R| := by
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBV0 : 0 ≤ BV :=
    mul_nonneg (inv_nonneg.2 (le_of_lt (sub_pos.2 h₀.2))) (abs_nonneg _)
  have hrm : ∀ k, Measurable (r k) := fun k => Random.Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Random.Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
      (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hr_bd : ∀ᵐ ω ∂(M θ), ∀ j, |r j ω| ≤ |M.env.R| := by
    have hcl : ∀ j,
        r j =ᵐ[M θ] fun ω => clip (ω j).1 (-M.env.R) M.env.R := fun j =>
      MEq_Clip.of.All_Eq.All_EqWithDensity h₁ (M := M) θ j
    have hcl' : ∀ᵐ ω ∂(M θ), ∀ j,
        r j ω = clip (ω j).1 (-M.env.R) M.env.R :=
      (ae_all_iff (ι := ℕ)).mpr hcl
    filter_upwards [hcl'] with ω hω j
    rw [hω j, ← Real.norm_eq_abs]
    exact NormClip.le.Abs_R (R := M.env.R) (ρ := (ω j).1)
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    filter_upwards [hr_bd] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hω (k + j)) (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BV
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV_ae : ∀ k,
      (fun ω => V[k] (s k ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s k)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact (hV k (s k ω)).trans hω
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |V[k] (s k ω)| ≤ BV := by
    have hcond : ∀ k, ∀ᵐ ω ∂(M θ),
        |Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BV := fun k => by
      have hbd :=
        ae_bdd_norm_condExp_of_ae_bdd_norm
          (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
          (m := MeasurableSpace.comap (s k) inferInstance)
          (by filter_upwards [hret_bd] with ω hω; exact hω k)
      filter_upwards [hbd] with ω h
      simpa [Expectation.condSigma, Real.norm_eq_abs] using h
    have hVeq := (ae_all_iff (ι := ℕ)).mpr hV_ae
    have hVnorm := (ae_all_iff (ι := ℕ)).mpr hcond
    filter_upwards [hVeq, hVnorm] with ω heq hnorm k
    rw [heq k]
    exact hnorm k
  have hB : (2 / (1 - γ)) * |M.env.R| = |M.env.R| + (1 + γ) * BV := by
    have hpos : 1 - γ ≠ 0 := (sub_pos.2 h₀.2).ne'
    simp [BV, div_eq_mul_inv, add_mul, mul_assoc]
    field_simp [hpos]
    ring
  filter_upwards [hr_bd, hVbd] with ω hr hv j
  rw [Real.norm_eq_abs]
  have hsum : |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
      |r j ω| + |γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
    have h1 := abs_add_le (r j ω) (γ * V[j + 1] (s (j + 1) ω))
    have h2 : |r j ω + γ * V[j + 1] (s (j + 1) ω) - V[j] (s j ω)| ≤
        |r j ω + γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (r j ω + γ * V[j + 1] (s (j + 1) ω)) (-V[j] (s j ω))
    exact h2.trans (add_le_add h1 le_rfl)
  have : |r j ω| + |γ * V[j + 1] (s (j + 1) ω)| + |V[j] (s j ω)| ≤
      |M.env.R| + (1 + γ) * BV := by
    have hγV : |γ * V[j + 1] (s (j + 1) ω)| ≤ γ * BV := by
      rw [abs_mul, abs_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hv (j + 1)) h₀.1
    have := add_le_add (add_le_add (hr j) hγV) (hv j)
    have hrew : γ * BV + BV = (1 + γ) * BV := by ring
    simpa [hrew, add_assoc] using this
  exact hsum.trans (this.trans_eq hB.symm)

/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438) for continuous actions:
with textbook `V[t] : 𝒮 → ℝ`, path-value `V_δ[t] δ k = V[t + k] (δ k)`, `ℓ ∈ [0, 1]`,
and score `∇ log ℙ(a[t] | s[t])`,
`∇𝔼[(γ ^ id) ⬝ᵥ r] = 𝔼[(γ ^ id) ⬝ᵥ fun t ↦ (((γ * ℓ) ^ id) ⬝ᵥ (r[t:] + γ • V_δ[t+1] s[t+1:] - V_δ[t] s[t:])) • ∇ log π]`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ ℓ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {V : ℕ ⇀ 𝒮 → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ℓ ∈ Set.Icc 0 1)
  (hfactor : DensityModel.IsConditionalProbability M r s a)
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob θ z.1 z.2))
  (hV : ∀ (k : ℕ) (x : 𝒮),
    V[k] x =
      Expectation.condEval (M θ) (fun ω : ℕ → ℝ × 𝒮 × 𝒜 => fun i => r i ω) (s k)
        (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) x)
  (h₂ : ∀ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)))
  (h₃ : ∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
      g «\sf{s}»[t] «\sf{a}»[t])
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)))
  (hMs : ∀ («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ ≤ Ms) :
-- imply
  letI : DensityModel.IsPolicyTrajectory M r s a := hfactor.htr
  letI : DensityModel.AbsContJointAS M a s := hfactor.haj
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hfactor.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_δ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => V[t + k] (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:])) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  intro _ _ _ _ V_δ
  -- `a` / `s` are still `ℕ ⇀` here; after `set` they are plain functions and `a[0]` is not GetElem
  have h₃' : ∀ θ' x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ'‖ ≤ g x u := by
    intro θ' x u
    have hfe : (fun θ => M.policy.prob θ x u) =
        (fun θ => (ℙ[M θ](a[0] = (⟨fun _ => u⟩ : ℕ ⇀ 𝒜)[0] |
          s[0] = (⟨fun _ => x⟩ : ℕ ⇀ 𝒮)[0]) : ℝ)) :=
      funext fun θ'' => hfactor.factor θ'' 0 x u
    have hgrad : ‖∇[θ'] M.policy.prob θ' x u‖ ≤ g x u := by
      simpa [hfe] using h₃ θ' 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using hgrad
  have hMspol : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms := by
    intro y u
    have hfe : (fun θ' => Real.log (M.policy.prob θ' y u)) =
        (fun θ' => (ℙ[M θ'](a[0] = (⟨fun _ => u⟩ : ℕ ⇀ 𝒜)[0] |
          s[0] = (⟨fun _ => y⟩ : ℕ ⇀ 𝒮)[0]) : ℝ).log) :=
      funext fun θ' => congrArg Real.log (hfactor.factor θ' 0 y u)
    simpa [hfe] using hMs ⟨fun _ => y⟩ ⟨fun _ => u⟩
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (hfactor.htr.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (hfactor.htr.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (hfactor.htr.stage_eq t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  let : MeasurableSpace Θ := borel Θ
  let : BorelSpace Θ := ⟨rfl⟩
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst hfactor.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd hfactor.htr.stage_eq t).aemeasurable⟩)
  have hc : γ * ℓ ∈ Set.Ico 0 1 :=
    ⟨mul_nonneg h₀.1 h₁.1, (mul_le_of_le_one_right h₀.1 h₁.2).trans_lt h₀.2⟩
  -- parent / Integral_SMul still take the dual (`fderiv`) form of the score
  have hφ' : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ) := by
    simpa [gradient] using
      (InnerProductSpace.toDual ℝ Θ).continuous.comp_stronglyMeasurable hφ
  have hMs' : ∀ y u,
    ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms := fun y u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hMspol y u
  set ψ : 𝒮 → 𝒜 → Θ →L[ℝ] ℝ := fun y u =>
    fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ
  have hψ : StronglyMeasurable (Function.uncurry ψ) := hφ'
  have hmeas : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
    (fun (s : ℕ → 𝒮) (_ : ℕ → 𝒜) (r : ℕ → ℝ) (k : ℕ) =>
        r k + γ * V[k + 1] (s (k + 1)) - V[k] (s k))
      (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k := fun k =>
    ((Random.Measurable.of.All_Eq.fst hfactor.htr.stage_eq k).add
      (((measurable_of_countable (V[k + 1])).comp
          (Random.Measurable.of.All_Eq.snd.fst hfactor.htr.stage_eq (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V[k])).comp
        (Random.Measurable.of.All_Eq.snd.fst hfactor.htr.stage_eq k))
  have hδall := ae_norm_residual (M := M) h₀ hfactor.htr.stage_eq θ hV
  set B1 : ℝ := (2 / (1 - γ)) * |M.env.R|
  have hbd : ∀ c ∈ Set.Ico (0 : ℝ) 1, ∀ᵐ ω ∂(M θ), ∀ t,
    ‖∑' k, c ^ k * (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
      V[t + k] (s (t + k) ω))‖ ≤
      (1 - c)⁻¹ * B1 := fun c hc' => by
    have hgeo := (hasSum_geometric_of_lt_one hc'.1 hc'.2).mul_right B1
    filter_upwards [hδall] with ω h t
    have hs : Summable fun k : ℕ =>
        ‖c ^ k * (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
          V[t + k] (s (t + k) ω))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => by
          rw [norm_mul, norm_pow, Real.norm_of_nonneg hc'.1]
          exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hc'.1 k))
        hgeo.summable
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    have hpt : ∀ k,
        ‖c ^ k * (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
          V[t + k] (s (t + k) ω))‖ ≤ c ^ k * B1 := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hc'.1]
      exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hc'.1 k)
    have htendB : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, c ^ i * B1) atTop
        (nhds (∑' k, c ^ k * B1)) := by
      simpa [hgeo.tsum_eq] using hgeo.tendsto_sum_nat
    have hsumle :
        (∑' k, ‖c ^ k * (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
          V[t + k] (s (t + k) ω))‖) ≤ ∑' k, c ^ k * B1 :=
      le_of_tendsto_of_tendsto hs.hasSum.tendsto_sum_nat htendB
        (Filter.Eventually.of_forall fun N =>
          Finset.sum_le_sum fun k _ => hpt k)
    exact hsumle.trans (hgeo.tsum_eq).le
  -- `c`-discounted advantage against the density score collapses to the first residual
  have hinner : ∀ c ∈ Set.Ico (0 : ℝ) 1, ∀ t, ∫ ω,
    (∑' k, c ^ k * (r (t + k) ω + γ * V[t + k + 1] (s (t + k + 1) ω) -
      V[t + k] (s (t + k) ω))) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
    ∫ ω, (r t ω + γ * V[t + 1] (s (t + 1) ω) - V[t] (s t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
    fun c hc' t =>
      Integral_SMul.of.In_Ico.In_Ico.All_EqWithDensity
        (M := M) h₀ hfactor.htr.stage_eq hπ θ hV hc' t ψ hψ ⟨Ms, hMs'⟩
  have hbase :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:])) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
      (M := M) h₀ hfactor.htr.stage_eq hπ hV
      (fun x u => (funext fun θ' => (hfactor.factor θ' 0 x u).symm) ▸ h₂ 0 ⟨fun _ => x⟩ ⟨fun _ => u⟩)
      h₃' h₄ h₅ hφ' hMs'
  -- rewrite V_δ sugar into pointwise residual form for dual conversion
  have hbaseexp :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ
            (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
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
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_δ,
      Function.getSliceFrom_apply, hk]
  -- Dot sugar ↔ path tsum sugar
  have hDotγ :
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ
            (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
      𝔼[r, s, a : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) ⬝ᵥ
              (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
  have hDotc :
    𝔼[r, s, a : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => (γ * ℓ) ^ k) ⬝ᵥ
              (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
            ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
            (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
    refine congrArg
      (Expectation.ofRV (M θ)
        (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) ?_
    funext integ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
  set Bγ : ℝ := (1 - γ)⁻¹ * B1
  set Bc : ℝ := (1 - γ * ℓ)⁻¹ * B1
  have hA₁ :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
      (M := M) (θ := θ) (γ := γ) (c := γ)
      (X := fun s _ r k => r k + γ * V[k + 1] (s (k + 1)) - V[k] (s k))
      (B := Bγ) (Ms := Ms) h₀ hfactor.htr.stage_eq hmeas (hbd γ h₀) hφ hMspol
  have hA₂ :=
    Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.All_Eq_Joint.All_EqWithDensity1
      (M := M) (θ := θ) (γ := γ) (c := γ * ℓ)
      (X := fun s _ r k => r k + γ * V[k + 1] (s (k + 1)) - V[k] (s k))
      (B := Bc) (Ms := Ms) h₀ hfactor.htr.stage_eq hmeas (hbd (γ * ℓ) hc) hφ hMspol
  have hsplit :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ
            (fun k => r (t + k) + γ * V[t + k + 1] (s (t + k + 1)) - V[t + k] (s (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) :=
    hbaseexp.trans (hDotγ.trans (hA₁.symm.trans
      ((congrArg (InnerProductSpace.toDual ℝ Θ).symm
          (tsum_congr fun t => by rw [hinner γ h₀ t, hinner (γ * ℓ) hc t])).trans
        (hA₂.trans hDotc))))
  have hPol :
    ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
      𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
        ((((γ * ℓ) ^ (id : ℕ → ℕ)) ⬝ᵥ (r[t:] + γ • V_δ[t + 1] s[t + 1:] - V_δ[t] s[t:])) •
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
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, V_δ,
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
      (funext fun θ' => congrArg Real.log (hfactor.factor θ' t (integ.2.1 t) (integ.2.2 t)))
  rw [hsc]
  congr 1


-- created on 2026-10-20
-- updated on 2026-11-11

import Notation.Fun
import Instance.Probability.SinglePSpaceMeasurable
import Instance.Algebra.Module.HDiv
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.ExpectSMul.eq.ExpectSMulExpectCond.of.All_LeNorm.StronglyMeasurable.All_Eq.All_EqWithDensity.In_Ico
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Random.Eq_WithDensity_Pdf
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Syntax.Order.Sup
import Instance.Analysis.Real.Numbers
import Instance.Dynamics.PolicyTrajectory
import Instance.Data.Nat.Fun
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 4000000

/-- `π • fderiv log π = fderiv π`, including where the density vanishes. -/
private lemma smul_fderiv_log
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (hdiff : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (θ : Θ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  M.π θ sₜ aₜ • fderiv ℝ (fun κ => Real.log (M.π κ sₜ aₜ)) θ =
    fderiv ℝ (fun κ => M.π κ sₜ aₜ) θ := by
-- proof
  if h : M.π θ sₜ aₜ = 0 then
    rw [h, zero_smul]
    exact (IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun κ => by
      rw [h]
      exact hStoch.nonneg κ sₜ aₜ)).symm
  else
    rw [fderiv.log ((hdiff sₜ aₜ) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- Partial sums of a discounted temporal-difference series telescope. -/
private lemma sum_td_telescope
-- given
  (γ : ℝ)
  (r v : ℕ → ℝ)
  (n : ℕ) :
-- imply
  ∑ k ∈ Finset.range n, γ ^ k * (r k + γ * v (k + 1) - v k) =
    ∑ k ∈ Finset.range n, γ ^ k * r k + γ ^ n * v n - v 0 := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- A bounded discounted temporal-difference series equals the return minus the initial value. -/
private lemma tsum_td_eq
  {γ : ℝ}
  {r v : ℕ → ℝ}
  {R B : ℝ}
-- given
  (hγ0 : 0 ≤ γ)
  (hγ1 : γ < 1)
  (hr : ∀ k, |r k| ≤ R)
  (hv : ∀ k, |v k| ≤ B) :
-- imply
  ∑' k, γ ^ k * (r k + γ * v (k + 1) - v k) =
    ∑' k, γ ^ k * r k - v 0 := by
-- proof
  have hR : 0 ≤ R := (abs_nonneg (r 0)).trans (hr 0)
  have hsumr : Summable (fun k => γ ^ k * r k) := by
    refine Summable.of_norm_bounded (g := fun k => γ ^ k * R) ?_ ?_
    · exact (summable_geometric_of_lt_one hγ0 hγ1).mul_right R
    ·
      intro k
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ0, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hr k) (pow_nonneg hγ0 k)
  set Bd : ℝ := R + (γ + 1) * B
  have hsumd : Summable (fun k => γ ^ k * (r k + γ * v (k + 1) - v k)) := by
    refine Summable.of_norm_bounded (g := fun k => γ ^ k * Bd) ?_ ?_
    · exact (summable_geometric_of_lt_one hγ0 hγ1).mul_right Bd
    ·
      intro k
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ0]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hγ0 k)
      calc
        _ ≤ ‖r k + γ * v (k + 1)‖ + ‖v k‖ := norm_sub_le _ _
        _ ≤ ‖r k‖ + ‖γ * v (k + 1)‖ + ‖v k‖ :=
          add_le_add (norm_add_le _ _) le_rfl
        _ ≤ R + γ * B + B := by
          rw [norm_mul, Real.norm_eq_abs γ, abs_of_nonneg hγ0, Real.norm_eq_abs (v (k + 1)),
            Real.norm_eq_abs (v k)]
          exact add_le_add (add_le_add (hr k) (mul_le_mul_of_nonneg_left (hv (k + 1)) hγ0)) (hv k)
        _ = Bd := by ring
  have hlim : Tendsto (fun n => γ ^ n * v n) atTop (nhds 0) := by
    have hbd : ∀ n, ‖γ ^ n * v n‖ ≤ γ ^ n * B := by
      intro n
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ0, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hv n) (pow_nonneg hγ0 n)
    suffices Tendsto (fun n => γ ^ n * B) atTop (nhds 0) by
      exact squeeze_zero_norm hbd this
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hγ0])).mul_const B
  refine HasSum.tsum_eq ?_
  rw [hsumd.hasSum_iff_tendsto_nat]
  have htele : ∀ n, ∑ k ∈ Finset.range n, γ ^ k * (r k + γ * v (k + 1) - v k) =
      ∑ k ∈ Finset.range n, γ ^ k * r k + γ ^ n * v n - v 0 :=
    fun n => sum_td_telescope γ r v n
  simp_rw [htele]
  simpa using ((hsumr.hasSum.tendsto_sum_nat).add hlim).sub_const (v 0)

/-- Along almost every trajectory, `|V_t(s_t)|` is bounded by the discounted reward envelope. -/

private lemma ae_bound_V
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ (1 - γ)⁻¹ * |R| := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set BV : ℝ := (1 - γ)⁻¹ * |R|
  have hrm : ∀ k, Measurable (r k) := fun k => Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
    (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ hR θ] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hω (k + j))
      (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BV
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hV_ae : ∀ k,
      (fun ω => M.V θ γ k (s k ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (s k)
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := s k)
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hsm k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact hω
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

/-- Almost every trajectory has temporal-difference return equal to the discounted reward minus `V`. -/

private lemma ae_td_eq_return
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ (1 - γ)⁻¹ * |R|)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (t : ℕ) :
-- imply
  ∀ᵐ ω ∂(M θ),
    ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
      M.V θ γ (t + k) (s (t + k) ω)) =
      ∑' k, γ ^ k * r (t + k) ω - M.V θ γ t (s t ω) := by
-- proof
  filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ hR θ, hVbd] with ω hr hv
  exact tsum_td_eq (r := fun k => r (t + k) ω)
    (v := fun k => M.V θ γ (t + k) (s (t + k) ω)) h₀.1 h₀.2
    (fun k => by simpa [Real.norm_eq_abs] using hr (t + k))
    (fun k => hv (t + k))

/-- Integral against a density-policy kernel is the reference integral weighted by `π`. -/
private lemma integral_kernel
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {f : 𝒜 → ℰ}
-- given
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  ∫ u, f u ∂(M[sₜ] θ) =
    ∫ u, M.π θ sₜ u • f u ∂μ.measure := by
-- proof
  have hπm : Measurable (M.pdf θ sₜ) :=
    (M.measurable_pdf θ).comp measurable_prodMk_left
  have hker : M[sₜ] θ =
      (μ.measure : Measure 𝒜).withDensity (M.pdf θ sₜ) :=
    Eq_WithDensity_Pdf (M := M) θ sₜ
  rw [hker, integral_withDensity_eq_integral_toReal_smul hπm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hnn : 0 ≤ M.π θ sₜ u := hStoch.nonneg θ sₜ u
  simp only [Policy.pdf]
  rw [ENNReal.toReal_ofReal hnn]

/-- Importance weight `π' • (c • (∇π / π'))` equals the on-policy score `π • (c • ∇ log π)`. -/
private lemma is_weight_eq_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
  {θ θ' : Θ}
-- given
  (hdiff : ∀ sₜ aₜ, Differentiable ℝ (fun κ => M.π κ sₜ aₜ))
  (hvanish : ∀ sₜ aₜ, M.π θ' sₜ aₜ ≠ 0 ∨ M.π θ sₜ aₜ = 0)
  (sₜ : 𝒮)
  (aₜ : 𝒜)
  (c : ℝ) :
-- imply
  M.π θ' sₜ aₜ •
      (c • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) =
    M.π θ sₜ aₜ • (c • ∇[θ] Real.log (M.π θ sₜ aₜ)) := by
-- proof
  let e : StrongDual ℝ Θ ≃ₗᵢ[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm
  if hq : M.π θ' sₜ aₜ = 0 then
    have hp : M.π θ sₜ aₜ = 0 := (hvanish sₜ aₜ).resolve_left (not_ne_iff.mpr hq)
    simp [hq, hp, HDiv.hDiv]
  else
    have hgrad := smul_fderiv_log (M := M) hdiff θ sₜ aₜ
    calc
      _ = c • ∇[θ] (M.π θ sₜ aₜ) := by
        simp only [HDiv.hDiv]
        rw [smul_smul, smul_smul]
        refine congrArg (fun t => t • ∇[θ] (M.π θ sₜ aₜ)) ?_
        rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
      _ = c • e (fderiv ℝ (fun κ => M.π κ sₜ aₜ) θ) := by
        simp [e, gradient]
      _ = e (c • fderiv ℝ (fun κ => M.π κ sₜ aₜ) θ) := by
        rw [map_smul]
      _ = e (c • (M.π θ sₜ aₜ •
          fderiv ℝ (fun κ => Real.log (M.π κ sₜ aₜ)) θ)) := by
        rw [← hgrad]
      _ = e ((M.π θ sₜ aₜ * c) •
          fderiv ℝ (fun κ => Real.log (M.π κ sₜ aₜ)) θ) := by
        rw [smul_smul, mul_comm]
      _ = M.π θ sₜ aₜ • (c •
          e (fderiv ℝ (fun κ => Real.log (M.π κ sₜ aₜ)) θ)) := by
        rw [smul_smul, map_smul]
      _ = M.π θ sₜ aₜ • (c • ∇[θ] Real.log (M.π θ sₜ aₜ)) := by
        simp [e, gradient]



/-- Scalar-vector division `c • (v / π')` is the inverse-smul form used by `AEStronglyMeasurable`. -/
private lemma smul_div_eq_inv_smul
    {ℰ : Type*} [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ]
    (c π' : ℝ) (v : ℰ) :
    c • (v / π') = π'⁻¹ • (c • v) := by
  simp [HDiv.hDiv, smul_smul, mul_comm]

private lemma div_smul_eq_smul_div
    {ℰ : Type*} [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ]
    (c π' : ℝ) (v : ℰ) :
    (c • v) / π' = c • (v / π') := by
  simp [HDiv.hDiv, smul_smul, mul_comm]


/-- A state-action score pulls out of the discounted return, via the tower property. -/
private lemma integral_return_smul_eq_cond
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ C : ℝ}
  {ψ : 𝒮 → 𝒜 → ℰ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : StronglyMeasurable (Function.uncurry ψ))
  (hC : ∀ y u, ‖ψ y u‖ ≤ C)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ)
  (t : ℕ) :
-- imply
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := r) (s := s) (a := a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := r) (s := s) (a := a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := r) (s := s) (a := a) h₁ t).aemeasurable⟩)
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s t ω ∧ a t = a t ω)) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  intro hsP haP hrP
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set Y := fun ω => (s t ω, a t ω)
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁ t
  have ha : Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁ t
  have hY : Measurable Y := hs.prodMk ha
  have hsa3 : Measurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦ (p.2.1 t, p.2.2 t) :=
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hGpath : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ p.1 (t + k)) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜))) => p.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst) γ t).stronglyMeasurable
  have hψpath3 : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → 𝒮) × (ℕ → 𝒜)) ↦
      ψ (p.2.1 t) (p.2.2 t) :=
    hψ.comp_measurable hsa3
  have hsa : Measurable fun p : (ℕ → 𝒮) × (ℕ → 𝒜) ↦ (p.1 t, p.2 t) :=
    ((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_snd)
  have hg : StronglyMeasurable
    (fun path : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (path : ℕ → ℝ) => path j)
      (fun j => measurable_pi_apply j) γ t).stronglyMeasurable
  have hEval : StronglyMeasurable
    (fun q : 𝒮 × 𝒜 ↦
      Expectation.condEval (M θ) (AsPathRV.path r) Y
        (fun path ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ path[t:]) q) := by
    simp only [Expectation.condEval]
    have hf : StronglyMeasurable
      (fun z : Prod (𝒮 × 𝒜) (ℕ → ℝ) ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ z.2[t:]) :=
      hg.comp_measurable measurable_snd
    exact hf.integral_condDistrib (Y := AsPathRV.path r) (X := Y) (μ := M θ)
  have hL :
    𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) • ψ (s t) (a t)) =
      ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) := by
    apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    exact (hGpath.smul hψpath3).aestronglyMeasurable
  have hRight :
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t], a[t]) • ψ (s t) (a t)) =
      ∫ ω, (𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s t ω ∧ a t = a t ω)) •
        ψ (s t ω) (a t ω) ∂(M θ) := by
    apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    exact ((hEval.smul hψ).comp_measurable hsa).aestronglyMeasurable
  refine hL.symm.trans (Eq.trans ?_ hRight)
  exact ExpectSMul.eq.ExpectSMulExpectCond.of.All_LeNorm.StronglyMeasurable.All_Eq.All_EqWithDensity.In_Ico
    (M := M) (ψ := ψ) (C := C) (r := r) (s := s) (a := a) h₀ h₁ hψ hC hR θ t

/-- The proposal kernel's Radon–Nikodym density is the policy probability, almost everywhere. -/
private lemma kernel_pdf
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ' : Θ)
  (sₜ : 𝒮)
  (hμ : (M[sₜ] θ' : Measure 𝒜) =
      (μ.measure : Measure 𝒜).withDensity (M.pdf θ' sₜ))
  (hpdf : Measurable (M.pdf θ' sₜ))
  (hSP : SinglePSpace (M[sₜ] θ') (id : 𝒜 → 𝒜)) :
-- imply
  (fun u => ((M[sₜ] θ').prob (id : 𝒜 → 𝒜) u).toReal) =ᵐ[μ.measure]
    M.π θ' sₜ := by
-- proof
  have hmap : (M[sₜ] θ').map (id : 𝒜 → 𝒜) =
      (μ.measure : Measure 𝒜).withDensity (M.pdf θ' sₜ) := by
    rw [Measure.map_id, hμ]
  have hrn :
    ((M[sₜ] θ').map (id : 𝒜 → 𝒜)).rnDeriv μ.measure =ᵐ[μ.measure]
      M.pdf θ' sₜ := by
    rw [hmap]
    exact Measure.rnDeriv_withDensity (ν := (μ.measure : Measure 𝒜)) hpdf
  filter_upwards [hrn] with u hu
  simp only [Measure.prob]
  have hnn : 0 ≤ M.π θ' sₜ u := hStoch.nonneg θ' sₜ u
  rw [hu]
  simp only [Policy.pdf]
  rw [ENNReal.toReal_ofReal hnn]

/-- Along almost every trajectory, `|Q_t(s_t, a_t)|` is bounded by the discounted reward envelope. -/
private lemma ae_bound_Q
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  [Nonempty 𝒜] [StandardBorelSpace 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1)
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, |M.Q θ γ k (s k ω) (a k ω)| ≤ (1 - γ)⁻¹ * |R| := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set BG : ℝ := (1 - γ)⁻¹ * |R|
  have hrm : ∀ k, Measurable (r k) := fun k => Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Measurable.of.All_Eq.snd.fst h₁ k
  have ham : ∀ k, Measurable (a k) := fun k => Measurable.of.All_Eq.snd.snd h₁ k
  have hY : ∀ k, Measurable fun ω => (s k ω, a k ω) := fun k => (hsm k).prodMk (ham k)
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
    (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BG := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ hR θ] with ω hω k
    refine tsum_of_norm_bounded hgeo fun j => ?_
    have hid : (γ ^ (id : ℕ → ℕ)) j = γ ^ j := rfl
    have hslice : (fun i => r i ω)[k:] j = r (k + j) ω := rfl
    rw [hid, hslice, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hω (k + j))
      (pow_nonneg h₀.1 j)
  have hret : ∀ k, Measurable fun ω : ℕ → ℝ × 𝒮 × 𝒜 =>
      (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:] := fun k =>
    (hfGret k).comp hpR
  have hGi : ∀ k,
      Integrable (fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:]) (M θ) :=
    fun k =>
      Integrable.of_bound (hret k).aestronglyMeasurable BG
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
  have hQ_ae : ∀ k,
      (fun ω => M.Q θ γ k (s k ω) (a k ω)) =ᵐ[M θ]
        Expectation.condSigma (M θ) (fun ω i => r i ω) (fun ω => (s k ω, a k ω))
          (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k => by
    have hcomp :=
      Expectation.condEval_comp_ae_eq_condSigma
        (x := fun ω i => r i ω) (y := fun ω => (s k ω, a k ω))
        (f := fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:])
        hpR.aemeasurable (hY k) (hfGret k).stronglyMeasurable (hGi k)
    filter_upwards [hcomp] with ω hω
    exact hω
  have hcond : ∀ k, ∀ᵐ ω ∂(M θ),
      |Expectation.condSigma (M θ) (fun ω i => r i ω) (fun ω => (s k ω, a k ω))
        (fun integ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) ω| ≤ BG := fun k => by
    have hbd :=
      ae_bdd_norm_condExp_of_ae_bdd_norm
        (f := fun ω => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun i => r i ω)[k:])
        (m := MeasurableSpace.comap (fun ω => (s k ω, a k ω)) inferInstance)
        (by filter_upwards [hret_bd] with ω hω; exact hω k)
    filter_upwards [hbd] with ω h
    simpa [Expectation.condSigma, Real.norm_eq_abs] using h
  have hQeq := (ae_all_iff (ι := ℕ)).mpr hQ_ae
  have hQnorm := (ae_all_iff (ι := ℕ)).mpr hcond
  filter_upwards [hQeq, hQnorm] with ω heq hnorm k
  rw [heq k]
  exact hnorm k

/-- `M.Q` agrees with the trajectory-coordinate form of the action-value under `h_all`. -/
private lemma Q_eq_expect
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h_all : ∀ (t : ℕ), (· t) = (r[t], s[t], a[t]))
  (θ : Θ)
  (γ : ℝ)
  (t : ℕ)
  (sₜ : 𝒮)
  (aₜ : 𝒜) :
-- imply
  M.Q θ γ t sₜ aₜ =
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = sₜ ∧ a[t] = aₜ) := by
-- proof
  have hr : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h_all t) ω)).symm
  have hs : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h_all t) ω)).symm
  have ha : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h_all t) ω)).symm
  unfold Model.Q
  simp only [Expectation.asRV_process, Expectation.asRV, hr, hs, ha, getElem_nat_apply]

/-- `M.V` agrees with the trajectory-coordinate form of the state-value under `h_all`. -/
private lemma V_eq_expect
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h_all : ∀ (t : ℕ), (· t) = (r[t], s[t], a[t]))
  (θ : Θ)
  (γ : ℝ)
  (t : ℕ)
  (sₜ : 𝒮) :
-- imply
  M.V θ γ t sₜ =
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = sₜ) := by
-- proof
  have hr : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h_all t) ω)).symm
  have hs : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h_all t) ω)).symm
  unfold Model.V
  simp only [Expectation.asRV_process, Expectation.asRV, hr, hs, getElem_nat_apply]

section
set_option linter.unusedVariables false

/--
Importance-sampled vanilla policy gradient (Schulman et al., arXiv 1506.02438, Proposition 1),
stated with the action value `Q` rather than the advantage.
Sampling the action from a proposal parameter `θ'` instead of `θ` replaces the score
`∇ log π_θ` by `∇π_θ / π_θ'`, provided `π_θ'` vanishes only where `π_θ` does.
The state marginal stays the one induced by `θ`.
The alphabets are general reference-measure spaces; the conclusion is written in
`ℙ` densities as `(Q • ∇ ℙ) / ℙ_proposal`.
A θ-independent integrable dominate `g` of `‖∇π‖`, with `sup[x] ∫ g < ∞`, replaces a
uniform bound on `‖∇π‖` that need not be integrable against an infinite alphabet.
`sup[y, u] ‖∇ log π_θ‖ < ∞` bounds the score.

- [continuous-action GAE](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  [Nonempty 𝒜] [StandardBorelSpace 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ θ' : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → 𝒮 → 𝒜 → ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {R : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ (t : ℕ), (· t) = (r[t], s[t], a[t]))
  (h₂ : ∀ θ t («\sf{s}» : ℕ → 𝒮) («\sf{a}» : ℕ → 𝒜), Q θ t «\sf{s}»[t] «\sf{a}»[t] = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = «\sf{s}»[t] ∧ a[t] = «\sf{a}»[t]))
  (h₃ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₄ : ∀ sₜ aₜ, M.π θ' sₜ aₜ ≠ 0 ∨ M.π θ sₜ aₜ = 0)
  (hg : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖) ∂μ.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) μ.measure)
  (hφ : StronglyMeasurable (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun κ => Real.log (M.π κ z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun κ => Real.log (M.π κ y u)) θ‖ < ∞)
  (hVm : ∀ k, Measurable (M.V θ γ k))
  (hQm : ∀ k, StronglyMeasurable (fun z : 𝒮 × 𝒜 => Q θ k z.1 z.2))
  (hSPas : ∀ κ (t : ℕ), SinglePSpace (M κ) (a t, s t))
  (hpieq : ∀ κ (t : ℕ) sₜ aₜ, ((M κ).condProb (a t, s t) (aₜ, sₜ)).toReal = M.π κ sₜ aₜ)
  (hR : ∀ p, (M.reward p : Measure ℝ) (Set.Icc (-R) R) = 1) :
-- imply
  have : ∀ θ (t : ℕ), SinglePSpace (M θ) (a t, s t) := hSPas
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  have hμker : ∀ (sₜ : 𝒮), (M[sₜ] θ' : Measure 𝒜) =
      (μ.measure : Measure 𝒜).withDensity (M.pdf θ' sₜ) :=
    Eq_WithDensity_Pdf (M := M) θ'
  have hpdf : ∀ (sₜ : 𝒮), Measurable (M.pdf θ' sₜ) := fun x =>
    (M.measurable_pdf θ').comp (Measurable.prodMk measurable_const measurable_id)
  have : ∀ (sₜ : 𝒮), PSpace (M[sₜ] θ') (id : 𝒜 → 𝒜) := fun x =>
    { aemeasurable := measurable_id.aemeasurable }
  have : ∀ (sₜ : 𝒮), SinglePSpace (M[sₜ] θ') (id : 𝒜 → 𝒜) := fun x =>
    SinglePSpace.of.AEMeasurable.Distributed
      (hpdf x)
      (by rw [Measure.map_id, hμker x])
      measurable_id.aemeasurable
  let s₀ := s
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        (Q θ t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
          (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ))) := by
-- proof
  intro hSP hsP haP hrP hμker hpdf hPker hSPker s₀
  let g : 𝒮 → 𝒜 → ℝ :=
    fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)
  have hsupG := hg
  have hg : ∀ κ sₜ aₜ, ‖fderiv ℝ (fun θ => M.π θ sₜ aₜ) κ‖ ≤ g sₜ aₜ := by
    intro κ sₜ aₜ
    have : ‖∇[κ] M.π κ sₜ aₜ‖ ≤ g sₜ aₜ := le_csSup (hBdd sₜ aₜ) ⟨κ, rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using this
  have hintg : ∀ x, Integrable (g x) μ.measure := fun x => hIntg x
  have hcg := hsupG
  obtain ⟨Cg, hcgbound⟩ := id hcg
  have hcgle : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hcgbound ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun κ => Real.log (M.π κ y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  have hQeq : ∀ t x u, Q θ t x u = M.Q θ γ t x u := fun t x u =>
    (h₂ θ t (fun _ => x) (fun _ => u)).trans
      (Q_eq_expect (M := M) h₁ θ γ t x u).symm
  let A : Θ → ℕ → 𝒮 → 𝒜 → ℝ := fun θ t x u => Q θ t x u - M.V θ γ t x
  have hAeq : ∀ θ t x u, A θ t x u = Q θ t x u - M.V θ γ t x :=
    fun _ _ _ _ => rfl
  have hmeas : ∀ κ, Measurable (fun z : 𝒮 × 𝒜 => M.π κ z.1 z.2) :=
    hStoch.measurable_π
  have hGAE :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
      (M := M) (θ := θ) (γ := γ) (r := r) (s := s) (a := a) h₀ h₁ hmeas hVm h₃ hsupG hBdd hIntg hφ hMs hR
  rw [hGAE]
  set BG : ℝ := (1 - γ)⁻¹ * |R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s[k] ω)| ≤ BG :=
    ae_bound_V (M := M) h₀ h₁ hR θ
  let e : StrongDual ℝ Θ ≃ₗᵢ[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm
  let L := e.toContinuousLinearEquiv
  have hgradLogB : ∀ y u, ‖∇[θ] Real.log (M.π θ y u)‖ ≤ Ms := fun y u => by
    simpa [gradient, e, LinearIsometryEquiv.norm_map] using hMsle y u
  have hg0 : ∀ x u, 0 ≤ g x u := fun x u => (norm_nonneg _).trans (hg θ x u)
  have hs_meas : ∀ (t : ℕ), Measurable (s t) := fun t => Measurable.of.All_Eq.snd.fst h₁ t
  have ha_meas : ∀ (t : ℕ), Measurable (a t) := fun t => Measurable.of.All_Eq.snd.snd h₁ t
  have hr_meas : ∀ (t : ℕ), Measurable (r t) := fun t => Measurable.of.All_Eq.fst h₁ t
  have hGbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG := by
    intro t
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ hR θ] with ω hr
    have hsum : Summable fun k => γ ^ k * |R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hr (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    have hG : ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω = ∑' k, γ ^ k * r (t + k) ω := by
      simp [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    rw [hG]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Measurable.of.All_Eq.fst h₁)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    intro t
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hpair_t : ∀ t, Measurable fun ω => (s t ω, a t ω) := fun t =>
    (hs_meas t).prodMk (ha_meas t)

  have hMQbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.Q θ γ k (s[k] ω) (a[k] ω)| ≤ BG :=
    ae_bound_Q (M := M) h₀ h₁ hR θ
  have hQbd : ∀ᵐ ω ∂(M θ), ∀ k, |Q θ k (s[k] ω) (a[k] ω)| ≤ BG := by
    filter_upwards [hMQbd] with ω h k
    simpa [hQeq] using h k
  have hAB_ae : ∀ t, ∀ᵐ ω ∂(M θ), ‖A θ t (s[t] ω) (a[t] ω)‖ ≤ 2 * BG := by
    intro t
    filter_upwards [hQbd, hVbd] with ω hq hv
    calc
      _ = ‖Q θ t (s[t] ω) (a[t] ω) - M.V θ γ t (s[t] ω)‖ := by rw [hAeq]
      _ ≤ ‖Q θ t (s[t] ω) (a[t] ω)‖ + ‖M.V θ γ t (s[t] ω)‖ := norm_sub_le _ _
      _ ≤ BG + BG := add_le_add (by simpa [Real.norm_eq_abs] using hq t)
          (by simpa [Real.norm_eq_abs] using hv t)
      _ = 2 * BG := by ring
  have hAm : ∀ t, StronglyMeasurable (fun z : 𝒮 × 𝒜 => A θ t z.1 z.2) := fun t =>
    (hQm t).sub ((hVm t).comp measurable_fst).stronglyMeasurable
  have hclipQ : Continuous fun x : ℝ => clip x (-BG) BG := by
    unfold clip
    exact (continuous_id.max continuous_const).min continuous_const
  let Qclip : ℕ → 𝒮 → 𝒜 → ℝ := fun t x u => clip (Q θ t x u) (-BG) BG
  have hQclipm : ∀ t, StronglyMeasurable (fun z : 𝒮 × 𝒜 => Qclip t z.1 z.2) := fun t =>
    (hclipQ.measurable.comp (hQm t).measurable).stronglyMeasurable
  have hQclip_bd : ∀ t x u, |Qclip t x u| ≤ BG := fun t x u =>
    abs_le.mpr ⟨le_min (le_max_right _ _) (neg_le_self hBG),
      min_le_right _ _⟩
  have hQclip_ae : ∀ t, (fun ω => Qclip t (s[t] ω) (a[t] ω)) =ᵐ[M θ]
      fun ω => Q θ t (s[t] ω) (a[t] ω) := fun t => by
    filter_upwards [hQbd] with ω h
    have hle : |Q θ t (s[t] ω) (a[t] ω)| ≤ BG := h t
    have hlo : -BG ≤ Q θ t (s[t] ω) (a[t] ω) := (abs_le.mp hle).1
    have hhi : Q θ t (s[t] ω) (a[t] ω) ≤ BG := (abs_le.mp hle).2
    change clip (Q θ t (s[t] ω) (a[t] ω)) (-BG) BG = Q θ t (s[t] ω) (a[t] ω)
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have hgradPiB : ∀ y u, ‖∇[θ] (M.π θ y u)‖ ≤ g y u := fun y u => by
    simpa [gradient, e, LinearIsometryEquiv.norm_map] using hg θ y u
  have hgradSm : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.π θ z.1 z.2)) := by
    simp only [gradient]
    exact e.continuous.comp_stronglyMeasurable hφ
  have hgrad_eq : ∀ y u,
      ∇[θ] (M.π θ y u) =
        M.π θ y u • ∇[θ] Real.log (M.π θ y u) := fun y u => by
    have hfd := smul_fderiv_log (M := M) h₃ θ y u
    simp only [gradient]
    rw [← hfd, map_smul]
  have hgradPiSm : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] (M.π θ z.1 z.2)) := by
    convert (hStoch.measurable_π θ).stronglyMeasurable.smul hgradSm using 1
    funext z
    exact hgrad_eq z.1 z.2
  let ψ : ℕ → 𝒮 → Θ := fun t x =>
    𝔼[a : M[x] θ'](
      (Q θ t x a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t] = x) : ℝ)) /
        (ℙ[M[x] θ'](a[t] | s[t] = x) : ℝ))
  have hRHS :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        (Q θ t s[t] a[t] • ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
          (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ))) =
      𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t s[t]) :=
    rfl
  rw [hRHS]
  let ψπc : ℕ → 𝒮 → Θ := fun t x =>
    𝔼[a : M[x] θ'](
      ((Qclip t x a[t] •
        ((∇[θ] (M.π θ x a[t])) /
          (ℙ[M[x] θ'](a[t] | s[t] = x) : ℝ)))))
  have hψπc_integral : ∀ t sₜ,
      ψπc t sₜ =
        ∫ aₜ, M.π θ sₜ aₜ •
          (Qclip t sₜ aₜ • ∇[θ] Real.log (M.π θ sₜ aₜ))
          ∂(μ.measure : Measure 𝒜) := by
    intro t sₜ
    have hx : Measurable (fun aₜ : 𝒜 => (sₜ, aₜ)) :=
      Measurable.prodMk measurable_const measurable_id
    have hA : StronglyMeasurable (fun aₜ : 𝒜 => Qclip t sₜ aₜ) :=
      (hQclipm t).comp_measurable hx
    have hπ' : Measurable (fun aₜ : 𝒜 => M.π θ' sₜ aₜ) :=
      (hStoch.measurable_π θ').comp hx
    have hgrad : StronglyMeasurable (fun aₜ : 𝒜 => ∇[θ] (M.π θ sₜ aₜ)) :=
      hgradPiSm.comp_measurable hx
    have hnum : StronglyMeasurable
      (fun aₜ : 𝒜 => Qclip t sₜ aₜ • ∇[θ] (M.π θ sₜ aₜ)) :=
      hA.smul hgrad
    have hSP : SinglePSpace (M[sₜ] θ') (id : 𝒜 → 𝒜) := hSPker sₜ
    have hpdf := kernel_pdf (M := M) θ' sₜ (hμker sₜ) (hpdf sₜ) hSP
    have hfπ : AEStronglyMeasurable
      (fun aₜ => Qclip t sₜ aₜ •
        ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ))
      (M[sₜ] θ' : Measure 𝒜) := by
      have heq :
          (fun aₜ => Qclip t sₜ aₜ •
            ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) =
          (fun aₜ => M.π θ' sₜ aₜ)⁻¹ •
            (fun aₜ => Qclip t sₜ aₜ • ∇[θ] (M.π θ sₜ aₜ)) := by
        funext u
        exact smul_div_eq_inv_smul _ _ _
      rw [heq]
      exact ((hπ'.inv.stronglyMeasurable).smul hnum).aestronglyMeasurable
    have hfP : AEStronglyMeasurable
      (fun aₜ => Qclip t sₜ aₜ •
        ((∇[θ] (M.π θ sₜ aₜ)) /
          ((M[sₜ] θ').prob (id : 𝒜 → 𝒜) aₜ).toReal))
      ((M[sₜ] θ').map (id : 𝒜 → 𝒜)) := by
      rw [Measure.map_id]
      refine hfπ.congr ?_
      have habs : (M[sₜ] θ') ≪ (μ.measure : Measure 𝒜) := by
        rw [hμker sₜ]
        exact withDensity_absolutelyContinuous _ _
      filter_upwards [habs.ae_le hpdf] with u hu
      rw [hu]
    simp only [ψπc]
    rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hfP]
    simp only [id]
    rw [integral_kernel (M := M) θ' sₜ]
    refine integral_congr_ae ?_
    filter_upwards [hpdf] with u hu
    rw [hu]
    exact is_weight_eq_score (M := M) h₃ h₄ sₜ u (Qclip t sₜ u)
  have hterm_clip : ∀ t sₜ aₜ,
      ‖M.π θ' sₜ aₜ •
        (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ))‖ ≤
        BG * g sₜ aₜ := by
    intro t sₜ aₜ
    if hq : M.π θ' sₜ aₜ = 0 then
      simp [hq, HDiv.hDiv]
      exact mul_nonneg hBG (hg0 sₜ aₜ)
    else
      have hcancel :
        M.π θ' sₜ aₜ •
          (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) =
          Qclip t sₜ aₜ • ∇[θ] (M.π θ sₜ aₜ) := by
        simp only [HDiv.hDiv]
        rw [smul_smul, smul_smul]
        refine congrArg (fun t => t • ∇[θ] (M.π θ sₜ aₜ)) ?_
        rw [mul_assoc, mul_comm (Qclip t sₜ aₜ), ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
      rw [hcancel, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hQclip_bd t sₜ aₜ) (hgradPiB sₜ aₜ) (norm_nonneg _) hBG
  have hψπcB : ∀ t x, ‖ψπc t x‖ ≤ BG * max Cg 0 := by
    intro t sₜ
    have heq :
        (fun aₜ => M.π θ sₜ aₜ •
          (Qclip t sₜ aₜ • ∇[θ] Real.log (M.π θ sₜ aₜ))) =
        fun aₜ => M.π θ' sₜ aₜ •
          (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) := by
      funext u
      exact (is_weight_eq_score (M := M) h₃ h₄ sₜ u (Qclip t sₜ u)).symm
    rw [hψπc_integral, heq]
    have hinterm : Integrable
      (fun aₜ => M.π θ' sₜ aₜ •
        (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)))
      (μ.measure : Measure 𝒜) := by
      have hx : Measurable (fun aₜ : 𝒜 => (sₜ, aₜ)) :=
        Measurable.prodMk measurable_const measurable_id
      have hA : StronglyMeasurable (fun aₜ : 𝒜 => Qclip t sₜ aₜ) :=
        (hQclipm t).comp_measurable hx
      have hπ' : Measurable (fun aₜ : 𝒜 => M.π θ' sₜ aₜ) :=
        (hStoch.measurable_π θ').comp hx
      have hgrad : StronglyMeasurable (fun aₜ : 𝒜 => ∇[θ] (M.π θ sₜ aₜ)) :=
        hgradPiSm.comp_measurable hx
      have hnum : StronglyMeasurable
        (fun aₜ : 𝒜 => Qclip t sₜ aₜ • ∇[θ] (M.π θ sₜ aₜ)) :=
        hA.smul hgrad
      have hsm : StronglyMeasurable
          (fun aₜ => M.π θ' sₜ aₜ •
            (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ))) := by
        have hinner : StronglyMeasurable
            (fun aₜ => Qclip t sₜ aₜ •
              ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) := by
          have heq :
              (fun aₜ => Qclip t sₜ aₜ •
                ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ)) =
              (fun aₜ => M.π θ' sₜ aₜ)⁻¹ •
                (fun aₜ => Qclip t sₜ aₜ • ∇[θ] (M.π θ sₜ aₜ)) := by
            funext u
            exact smul_div_eq_inv_smul _ _ _
          rw [heq]
          exact (hπ'.inv.stronglyMeasurable).smul hnum
        exact hπ'.stronglyMeasurable.smul hinner
      exact ((hintg sₜ).smul (BG)).mono' hsm.aestronglyMeasurable
        (Filter.Eventually.of_forall (hterm_clip t sₜ))
    have hle : ‖∫ aₜ, M.π θ' sₜ aₜ •
        (Qclip t sₜ aₜ • ((∇[θ] (M.π θ sₜ aₜ)) / M.π θ' sₜ aₜ))
        ∂(μ.measure : Measure 𝒜)‖ ≤
        ∫ u, BG * g sₜ u ∂(μ.measure : Measure 𝒜) :=
      norm_integral_le_of_norm_le ((hintg sₜ).smul (BG))
        (Filter.Eventually.of_forall (hterm_clip t sₜ))
    have hmul : ∫ u, BG * g sₜ u ∂(μ.measure : Measure 𝒜) =
        BG * ∫ u, g sₜ u ∂(μ.measure : Measure 𝒜) := by
      simpa [smul_eq_mul] using integral_smul (BG) (g sₜ)
    have hcg' : ∫ u, g sₜ u ∂(μ.measure : Measure 𝒜) ≤ max Cg 0 :=
      (hcgle sₜ).trans (le_max_left _ _)
    calc
      _ ≤ BG * ∫ u, g sₜ u ∂(μ.measure : Measure 𝒜) := by
        rwa [hmul] at hle
      _ ≤ BG * max Cg 0 :=
        mul_le_mul_of_nonneg_left hcg' hBG
  have hφAc : ∀ t, StronglyMeasurable
    (Function.uncurry fun y u =>
      Qclip t y u • ∇[θ] Real.log (M.π θ y u)) := fun t =>
    ((hQclipm t).smul hgradSm)
  have hCφc : ∀ t y u,
      ‖Qclip t y u • ∇[θ] Real.log (M.π θ y u)‖ ≤ BG * max Ms 0 :=
    fun t y u => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hQclip_bd t y u) ((hgradLogB y u).trans (le_max_left _ _))
        (norm_nonneg _) hBG
  have hinnerC_m : ∀ t, StronglyMeasurable (ψπc t) := fun t => by
    have hf : StronglyMeasurable
      (Function.uncurry fun (y : 𝒮) (aₜ : 𝒜) =>
        M.π θ y aₜ •
          (Qclip t y aₜ • ∇[θ] Real.log (M.π θ y aₜ))) :=
      ((hStoch.measurable_π θ).stronglyMeasurable.smul (hφAc t))
    convert hf.integral_prod_right (ν := (μ.measure : Measure 𝒜)) using 1
    funext y
    exact hψπc_integral t y
  have hinner_clip : ∀ t, ∀ᵐ y ∂((M θ).map s[t]), ψ t y = ψπc t y := by
    intro t
    have hbad : ∫ ω,
        (if |Q θ t (s t ω) (a t ω)| ≤ BG then (0 : ℝ) else 1) ∂(M θ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hQbd] with ω h
      have h' : |Q θ t (s t ω) (a t ω)| ≤ BG := by
        simpa only [getElem_nat_apply] using h t
      simp [h']
    have hφind : StronglyMeasurable
      (Function.uncurry fun y u =>
        (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)) := by
      have hA : Measurable (fun z : 𝒮 × 𝒜 => Q θ t z.1 z.2) := (hQm t).measurable
      apply Measurable.stronglyMeasurable
      apply Measurable.ite
      ·
        have hEq : {z : 𝒮 × 𝒜 | |Q θ t z.1 z.2| ≤ BG} =
            (fun z : 𝒮 × 𝒜 => Q θ t z.1 z.2) ⁻¹' Set.Icc (-BG) (BG) := by
          ext z; simp [abs_le, Set.mem_preimage, Set.mem_Icc]
        rw [hEq]
        exact hA measurableSet_Icc
      · exact measurable_const
      · exact measurable_const
    have hdis0 :=
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
        (M := M) (ℰ := ℝ)
        (φ := fun y u => if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
        (C := (1 : ℝ)) h₁ hφind (fun y u => by
          if h : |Q θ t y u| ≤ BG then
            simp [h]
          else
            simp [h]) θ t
    have hinter0 :
      ∫ y, (∫ u, M.π θ y u •
          (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
        ∂(μ.measure : Measure 𝒜)) ∂((M θ).map s[t]) = 0 := by
      simpa [hbad] using hdis0.symm
    have hnn : ∀ y,
        0 ≤ ∫ u, M.π θ y u •
          (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
          ∂(μ.measure : Measure 𝒜) := fun y =>
      integral_nonneg fun u =>
        mul_nonneg (hStoch.nonneg θ y u) (dite_nonneg (fun _ => le_rfl) (fun _ => zero_le_one))
    have hy0 : ∀ᵐ y ∂((M θ).map s[t]),
        ∫ u, M.π θ y u •
          (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
          ∂(μ.measure : Measure 𝒜) = 0 := by
      apply (integral_eq_zero_iff_of_nonneg hnn _).1 hinter0
      have hfite : StronglyMeasurable
        (Function.uncurry fun (y : 𝒮) (aₜ : 𝒜) =>
          M.π θ y aₜ *
            (if |Q θ t y aₜ| ≤ BG then (0 : ℝ) else 1)) :=
        ((hStoch.measurable_π θ).mul hφind.measurable).stronglyMeasurable
      have hsmY' : StronglyMeasurable
        (fun y => ∫ u, M.π θ y u •
          (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
          ∂(μ.measure : Measure 𝒜)) :=
        hfite.integral_prod_right (ν := (μ.measure : Measure 𝒜))
      refine Integrable.of_bound hsmY'.aestronglyMeasurable 1 ?_
      refine Eventually.of_forall fun y => ?_
      have hrew := integral_kernel (M := M)
        (f := fun u => if |Q θ t y u| ≤ BG then (0 : ℝ) else 1) θ y
      have hle :
        ∫ u, (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1) ∂(M[y] θ) ≤
          ∫ u, (1 : ℝ) ∂(M[y] θ) := by
        refine integral_mono_of_nonneg
          (Eventually.of_forall fun u => by
            if h : |Q θ t y u| ≤ BG then
              simp [h]
            else
              simp [h])
          (integrable_const (1 : ℝ))
          (Eventually.of_forall fun u => by
            if h : |Q θ t y u| ≤ BG then
              simp [h]
            else
              simp [h])
      rw [← hrew]
      have hnn' : 0 ≤ ∫ u, (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1) ∂(M[y] θ) :=
        integral_nonneg fun u => by
          if h : |Q θ t y u| ≤ BG then
            simp [h]
          else
            simp [h]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn']
      apply hle.trans
      apply le_of_eq
      have : IsProbabilityMeasure (M[y] θ : Measure 𝒜) := inferInstance
      simp [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        smul_eq_mul]
    -- For a.e. y, π vanishes or |A| ≤ 2*BG a.e. [μ], so clip is invisible under π,
    -- and the unclipped IS inner expectation equals the clipped integral.
    have hμθ : ∀ (sₜ : 𝒮), (M[sₜ] θ : Measure 𝒜) =
        (μ.measure : Measure 𝒜).withDensity (M.pdf θ sₜ) :=
      Eq_WithDensity_Pdf (M := M) θ
    have hpdfθ : ∀ (sₜ : 𝒮), Measurable (M.pdf θ sₜ) := fun x =>
      (M.measurable_pdf θ).comp (Measurable.prodMk measurable_const measurable_id)
    filter_upwards [hy0] with y hy
    have hu : ∀ᵐ u ∂(μ.measure : Measure 𝒜),
        M.π θ y u = 0 ∨ |Q θ t y u| ≤ BG := by
      have hmul :
        ∫ u, M.π θ y u * (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1)
          ∂(μ.measure : Measure 𝒜) = 0 := by
        simpa [smul_eq_mul] using hy
      have hnn' : 0 ≤ fun u =>
          M.π θ y u * (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1) := fun u =>
        mul_nonneg (hStoch.nonneg θ y u) (dite_nonneg (fun _ => le_rfl) (fun _ => zero_le_one))
      have hAμ : Measurable fun aₜ : 𝒜 => Q θ t y aₜ :=
        (hQm t).measurable.comp (Measurable.prodMk measurable_const measurable_id)
      have hsetμ : MeasurableSet {aₜ : 𝒜 | |Q θ t y aₜ| ≤ BG} := by
        have hEq : {aₜ : 𝒜 | |Q θ t y aₜ| ≤ BG} =
            (fun aₜ : 𝒜 => Q θ t y aₜ) ⁻¹' Set.Icc (-BG) (BG) := by
          ext u; simp [abs_le, Set.mem_preimage, Set.mem_Icc]
        rw [hEq]
        exact hAμ measurableSet_Icc
      have hindμ : Measurable fun aₜ : 𝒜 =>
          (if |Q θ t y aₜ| ≤ BG then (0 : ℝ) else 1) :=
        measurable_const.ite hsetμ measurable_const
      have hπint : Integrable (M.π θ y) μ.measure := by
        have h1 : Integrable (fun _ : 𝒜 => (1 : ℝ)) (M[y] θ) := integrable_const 1
        rw [hμθ y] at h1
        have h' :=
          (integrable_withDensity_iff (μ := μ.measure)
            (f := M.pdf θ y) (hpdfθ y)
            (Eventually.of_forall fun u => by
              simp [Policy.pdf, ENNReal.ofReal_lt_top])).1 h1
        convert h' using 1
        funext aₜ
        have hnn : 0 ≤ M.π θ y aₜ := hStoch.nonneg θ y aₜ
        simp only [Policy.pdf]
        rw [ENNReal.toReal_ofReal hnn, one_mul]
      have hprodint : Integrable
        (fun u => M.π θ y u *
          (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1))
        μ.measure :=
        Integrable.mono' hπint
          (((hStoch.measurable_π θ).comp
            (Measurable.prodMk measurable_const measurable_id)).mul hindμ).aestronglyMeasurable
          (Eventually.of_forall fun u => by
            have hπ0 : 0 ≤ M.π θ y u := hStoch.nonneg θ y u
            if h : |Q θ t y u| ≤ BG then
              simp [h, hπ0]
            else
              simp [h, abs_of_nonneg hπ0])
      have hz :=
        (integral_eq_zero_iff_of_nonneg hnn' hprodint).1 (by simpa using hmul)
      filter_upwards [hz] with u hu
      if hπ0 : M.π θ y u = 0 then
        exact Or.inl hπ0
      else
        refine Or.inr ?_
        by_contra hgt
        have hite : (if |Q θ t y u| ≤ BG then (0 : ℝ) else 1) = 1 := by
          simp [hgt]
        have : M.π θ y u * 1 = 0 := by simpa [hite] using hu
        exact hπ0 (by simpa using this)
    -- ψ y as unclipped OfRV, rewritten with hpieq / kernel_pdf, equals the clipped integral
    have hSP : SinglePSpace (M[y] θ') (id : 𝒜 → 𝒜) := hSPker y
    have hpdf := kernel_pdf (M := M) θ' y (hμker y) (hpdf y) hSP
    have hnum_eq : ∀ u,
        ∇[θ] ((M θ).condProb (a t, s[t]) (u, y)).toReal =
          ∇[θ] (M.π θ y u) := fun u => by
      refine congrArg (gradient · θ) ?_
      funext κ
      exact hpieq κ t y u
    have hψw :
      ψ t y =
        Expectation.ofRV (M[y] θ') (id : 𝒜 → 𝒜)
          (fun u => (Q θ t y u • ∇[θ] (M.π θ y u)) /
            ((M[y] θ').prob (id : 𝒜 → 𝒜) u).toReal) := by
      simp only [ψ]
      refine congrArg (Expectation.ofRV (M[y] θ') id) ?_
      funext u
      simp only [hnum_eq]
    -- Show OfRV unclipped = ∫ π • (Qclip • ∇log) using a.e. agreement and is_weight
    have hx : Measurable (fun aₜ : 𝒜 => (y, aₜ)) :=
      Measurable.prodMk measurable_const measurable_id
    have hA : StronglyMeasurable (fun aₜ : 𝒜 => Qclip t y aₜ) :=
      (hQclipm t).comp_measurable hx
    have hπ' : Measurable (fun aₜ : 𝒜 => M.π θ' y aₜ) :=
      (hStoch.measurable_π θ').comp hx
    have hgrad : StronglyMeasurable (fun aₜ : 𝒜 => ∇[θ] (M.π θ y aₜ)) :=
      hgradPiSm.comp_measurable hx
    have hnum : StronglyMeasurable
      (fun aₜ : 𝒜 => Qclip t y aₜ • ∇[θ] (M.π θ y aₜ)) :=
      hA.smul hgrad
    have hfπ : AEStronglyMeasurable
      (fun u => Qclip t y u •
        ((∇[θ] (M.π θ y u)) / M.π θ' y u))
      (M[y] θ' : Measure 𝒜) := by
      have heq :
          (fun u => Qclip t y u •
            ((∇[θ] (M.π θ y u)) / M.π θ' y u)) =
          (fun u => M.π θ' y u)⁻¹ •
            (fun u => Qclip t y u • ∇[θ] (M.π θ y u)) := by
        funext u
        exact smul_div_eq_inv_smul _ _ _
      rw [heq]
      exact ((hπ'.inv.stronglyMeasurable).smul hnum).aestronglyMeasurable
    have hAuc : StronglyMeasurable (fun aₜ : 𝒜 => Q θ t y aₜ) :=
      (hQm t).comp_measurable hx
    have hnumu : StronglyMeasurable
      (fun aₜ : 𝒜 => Q θ t y aₜ • ∇[θ] (M.π θ y aₜ)) :=
      hAuc.smul hgrad
    have hfπu : AEStronglyMeasurable
      (fun u => (Q θ t y u • ∇[θ] (M.π θ y u)) /
        M.π θ' y u)
      (M[y] θ' : Measure 𝒜) := by
      have heq :
          (fun u => (Q θ t y u • ∇[θ] (M.π θ y u)) /
            M.π θ' y u) =
          (fun u => M.π θ' y u)⁻¹ •
            (fun u => Q θ t y u • ∇[θ] (M.π θ y u)) := by
        funext u
        simp [HDiv.hDiv]
      rw [heq]
      exact ((hπ'.inv.stronglyMeasurable).smul hnumu).aestronglyMeasurable
    have hfPu : AEStronglyMeasurable
      (fun u => (Q θ t y u • ∇[θ] (M.π θ y u)) /
        ((M[y] θ').prob (id : 𝒜 → 𝒜) u).toReal)
      ((M[y] θ').map (id : 𝒜 → 𝒜)) := by
      rw [Measure.map_id]
      refine hfπu.congr ?_
      have habs : (M[y] θ') ≪ (μ.measure : Measure 𝒜) := by
        rw [hμker y]
        exact withDensity_absolutelyContinuous _ _
      filter_upwards [habs.ae_le hpdf] with u hu
      rw [hu]
    rw [hψw, OfRV.eq.Integral.of.AEStronglyMeasurable_Map hfPu]
    simp only [id]
    rw [integral_kernel (M := M) θ' y]
    refine (integral_congr_ae ?_).trans (hψπc_integral t y).symm
    filter_upwards [hpdf, hu] with u huP huA
    rw [huP, div_smul_eq_smul_div]
    if hp : M.π θ y u = 0 then
      have hscore := is_weight_eq_score (M := M) h₃ h₄ y u (Q θ t y u)
      have hscorec := is_weight_eq_score (M := M) h₃ h₄ y u (Qclip t y u)
      have hgrad0 : ∇[θ] (M.π θ y u) = 0 := by
        have : fderiv ℝ (fun κ => M.π κ y u) θ = 0 :=
          IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun κ =>
            show M.π θ y u ≤ M.π κ y u from
              hp ▸ hStoch.nonneg κ y u)
        simpa [gradient] using this
      simp [hp, hgrad0, HDiv.hDiv]
    else
      have hle : |Q θ t y u| ≤ BG := huA.resolve_left hp
      have hlo : -BG ≤ Q θ t y u := (abs_le.mp hle).1
      have hhi : Q θ t y u ≤ BG := (abs_le.mp hle).2
      have hceq : Qclip t y u = Q θ t y u := by
        change clip (Q θ t y u) (-BG) BG = Q θ t y u
        rw [clip, max_eq_left hlo, min_eq_left hhi]
      rw [hceq]
      exact is_weight_eq_score (M := M) h₃ h₄ y u (Q θ t y u)

  have hdot_state :
      AEStronglyMeasurable
        (fun integ : ℕ → 𝒮 => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπc t (integ t))
        ((M θ).map (AsPathRV.path s)) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      ((hinnerC_m t).comp_measurable (measurable_pi_apply t)).const_smul
        (γ ^ t)).aestronglyMeasurable
  have hψπc_int :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπc t s[t]) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπc t (s[t] ω)) ∂(M θ) := by
    have : PSpace (M θ) (AsPathRV.path s) := hsP
    refine (OfRV.eq.Integral.of.AEStronglyMeasurable_Map hdot_state).trans ?_
    simp only [AsPathRV.path_process, getElem_nat_apply]
  have hψ_ae : ∀ᵐ ω ∂(M θ), ∀ t, ψ t (s t ω) = ψπc t (s t ω) := by
    have h := (ae_all_iff (ι := ℕ)).mpr fun t =>
      ae_of_ae_map (hs_meas t).aemeasurable (hinner_clip t)
    simpa only [getElem_nat_apply] using h
  have hψ_ofRV :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t s[t]) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπc t (s[t] ω)) ∂(M θ) := by
    have hpS : Measurable (AsPathRV.path s) := Measurable.of_eval hs_meas
    have hpath_t : ∀ t, s[t] = (fun σ : ℕ → 𝒮 => σ t) ∘ AsPathRV.path s := fun t => by
      funext ω
      rfl
    have htσ : ∀ t, ∀ᵐ σ ∂((M θ).map (AsPathRV.path s)),
        ψ t (σ t) = ψπc t (σ t) := fun t => by
      have hcomp : Measure.map (s[t]) (M θ) =
          Measure.map (fun σ : ℕ → 𝒮 => σ t) ((M θ).map (AsPathRV.path s)) := by
        rw [Measure.map_map (measurable_pi_apply t) hpS]
        exact congrArg (fun f => Measure.map f (M θ)) (hpath_t t)
      have hclip := hinner_clip t
      rw [hcomp] at hclip
      exact ae_of_ae_map (measurable_pi_apply t).aemeasurable hclip
    have hae : ∀ᵐ (σ : ℕ → 𝒮) ∂((M θ).map (AsPathRV.path s)),
        (∑' t, γ ^ t • ψ t (σ t)) =
          ∑' t, γ ^ t • ψπc t (σ t) := by
      filter_upwards [(ae_all_iff (ι := ℕ)).mpr htσ] with σ hσ
      exact tsum_congr fun t => by rw [hσ t]
    have hf : AEStronglyMeasurable
      (fun σ : ℕ → 𝒮 => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t (σ t))
      ((M θ).map (AsPathRV.path s)) :=
      hdot_state.congr (by
        filter_upwards [hae] with σ hσ
        simp only [Dot.dot, Function.hPow_apply, id_eq]
        exact hσ.symm)
    have : PSpace (M θ) (AsPathRV.path s) := hsP
    refine (OfRV.eq.Integral.of.AEStronglyMeasurable_Map hf).trans ?_
    simp only [AsPathRV.path_process]
    refine integral_congr_ae ?_
    filter_upwards [hψ_ae] with ω hω
    simp only [Dot.dot, Function.hPow_apply, id_eq, getElem_nat_apply, hω]
  rw [hψ_ofRV]

  have hclipm : Measurable fun x : ℝ => clip x (-BG) BG := by
    simp only [clip]
    exact (continuous_min.comp
      ((continuous_max.comp (continuous_id.prodMk continuous_const)).prodMk
        continuous_const)).measurable
  have hclip_le : ∀ x, ‖clip x (-BG) BG‖ ≤ BG := fun x => by
    have hlo : -BG ≤ clip x (-BG) BG := by
      simp only [clip]
      exact le_min (le_max_right _ _) (neg_le_self hBG)
    refine abs_le.2 ⟨hlo, ?_⟩
    simp only [clip]
    exact min_le_right _ _
  have htd_meas : ∀ t, Measurable fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
      ∑' k, γ ^ k * (integ.1 (t + k) + γ * M.V θ γ (t + k + 1) (integ.2.1 (t + k + 1)) -
        M.V θ γ (t + k) (integ.2.1 (t + k))) := by
    intro t
    refine Measurable.tsum fun k => ?_
    have hr : Measurable fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
        integ.1 (t + k) := (measurable_pi_apply (t + k)).comp measurable_fst
    have hs1 : Measurable fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
        integ.2.1 (t + k + 1) :=
      (measurable_pi_apply (t + k + 1)).comp (measurable_fst.comp measurable_snd)
    apply Measurable.const_mul
    apply Measurable.sub
    · exact (hr.add (((hVm (t + k + 1)).comp hs1).const_mul γ))
    · exact (hVm (t + k)).comp ((measurable_pi_apply (t + k)).comp (measurable_fst.comp measurable_snd))
  have hpair_path : ∀ t, Measurable fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
      (integ.2.1 t, integ.2.2 t) := fun t =>
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hLHS_sm : AEStronglyMeasurable
    (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
      ∑' t, γ ^ t •
        ((∑' k, γ ^ k * (integ.1 (t + k) + γ * M.V θ γ (t + k + 1) (integ.2.1 (t + k + 1)) -
            M.V θ γ (t + k) (integ.2.1 (t + k)))) •
          ∇[θ] Real.log (M.π θ (integ.2.1 t) (integ.2.2 t))))
    ((M θ).map (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) :=
    (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      ((htd_meas t).stronglyMeasurable.smul
        (hgradSm.comp_measurable (hpair_path t))).const_smul (γ ^ t)).aestronglyMeasurable
  have hfun :
    (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t =>
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ
          ((integ.1)[t:] +
            γ • (fun k => M.V θ γ (t + 1 + k) ((integ.2.1)[t + 1:] k)) -
            fun k => M.V θ γ (t + k) ((integ.2.1)[t:] k))) •
          ∇[θ] Real.log (M.π θ (integ.2.1 t) (integ.2.2 t)))) =
    (fun integ =>
      ∑' t, γ ^ t •
        ((∑' k, γ ^ k * (integ.1 (t + k) + γ * M.V θ γ (t + k + 1) (integ.2.1 (t + k + 1)) -
            M.V θ γ (t + k) (integ.2.1 (t + k)))) •
          ∇[θ] Real.log (M.π θ (integ.2.1 t) (integ.2.2 t)))) := by
    funext integ
    simp [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    refine tsum_congr fun t => ?_
    congr 1
    congr 1
    refine tsum_congr fun k => ?_
    simp [add_assoc, add_comm, add_left_comm]
  try simp only [hfun, getElem_nat_apply]
  rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hLHS_sm]
  simp only [JointRandomSymbol, Expectation.asRV, AsPathRV.path_process, Dot.dot,
    Function.hPow_apply, id_eq]
  have htd_ae : ∀ᵐ ω ∂(M θ), ∀ t,
      ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω)) =
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s t ω) := by
    rw [ae_all_iff]
    intro t
    filter_upwards [ae_td_eq_return (M := M) h₀ h₁ hVbd hR t] with ω hω
    simpa [Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom] using hω
  have hTDbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))‖ ≤ 2 * BG := by
    intro t
    filter_upwards [htd_ae, hGbd t, hVbd] with ω htd hG hV
    have htdt := htd t
    rw [htdt]
    calc
      _ ≤ ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ + ‖M.V θ γ t (s t ω)‖ :=
        norm_sub_le _ _
      _ ≤ BG + BG := add_le_add hG (by simpa [Real.norm_eq_abs] using hV t)
      _ = 2 * BG := by ring
  set Cψ : ℝ := BG * max Cg 0
  set Cl : ℝ := 2 * BG * max Ms 0
  have hCl0 : 0 ≤ Cl :=
    mul_nonneg (mul_nonneg (by norm_num) hBG) (le_max_right _ _)
  have hCψ0 : 0 ≤ Cψ :=
    mul_nonneg hBG (le_max_right _ _)
  have hMs0 : ∀ y u, ‖∇[θ] Real.log (M.π θ y u)‖ ≤ max Ms 0 :=
    fun y u => (hgradLogB y u).trans (le_max_left _ _)

  have hψπc_Fint : ∀ t, Integrable (fun ω => γ ^ t • ψπc t (s t ω)) (M θ) := by
    intro t
    refine Integrable.of_bound ?_ (γ ^ t * Cψ) ?_
    · exact (((hinnerC_m t).comp_measurable (hs_meas t)).const_smul (γ ^ t)).aestronglyMeasurable
    ·
      refine Eventually.of_forall fun ω => ?_
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
      exact mul_le_mul_of_nonneg_left (hψπcB t (s t ω)) (pow_nonneg h₀.1 t)
  have hψπc_sum : Summable fun t => ∫ ω, ‖γ ^ t • ψπc t (s t ω)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun t => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right Cψ)
    have hle : ∀ᵐ ω ∂(M θ), ‖γ ^ t • ψπc t (s t ω)‖ ≤ γ ^ t * Cψ :=
      Eventually.of_forall fun ω => by
        rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
        exact mul_le_mul_of_nonneg_left (hψπcB t (s t ω)) (pow_nonneg h₀.1 t)
    calc
      _ ≤ ∫ _, γ ^ t * Cψ ∂(M θ) :=
        integral_mono_ae (hψπc_Fint t).norm (integrable_const _) hle
      _ = γ ^ t * Cψ := by
        rw [integral_const]
        simp
  have hRHS_tsum :
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπc t (s t ω)) ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, ψπc t (s t ω) ∂(M θ) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [← integral_tsum_of_summable_integral_norm hψπc_Fint hψπc_sum]
    refine tsum_congr fun t => integral_smul (γ ^ t) _
  have hLterm_sm : ∀ t, StronglyMeasurable fun ω =>
      (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) := by
    intro t
    refine (Measurable.tsum fun k => ?_).stronglyMeasurable.smul
      (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))
    apply (((hr_meas (t + k)).add
      (((hVm (t + k + 1)).comp (hs_meas (t + k + 1))).const_mul γ)).sub
      ((hVm (t + k)).comp (hs_meas (t + k)))).const_mul (γ ^ k)
  have hLFint : ∀ t, Integrable (fun ω =>
      γ ^ t •
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω)))) (M θ) := by
    intro t
    refine Integrable.of_bound ((hLterm_sm t).const_smul (γ ^ t)).aestronglyMeasurable
      (γ ^ t * Cl) ?_
    filter_upwards [hTDbd t] with ω htd
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    exact mul_le_mul htd (hMs0 (s t ω) (a t ω)) (norm_nonneg _)
      (mul_nonneg (by norm_num) hBG)
  have hLbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t •
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω)))‖ ≤
        γ ^ t * Cl := by
    intro t
    filter_upwards [hTDbd t] with ω htd
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    exact mul_le_mul htd (hMs0 (s t ω) (a t ω)) (norm_nonneg _)
      (mul_nonneg (by norm_num) hBG)
  have hLsum : Summable fun t => ∫ ω, ‖γ ^ t •
      ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)))‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun t => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right Cl)
    calc
      _ ≤ ∫ _, γ ^ t * Cl ∂(M θ) :=
        integral_mono_ae (hLFint t).norm (integrable_const _) (hLbd t)
      _ = γ ^ t * Cl := by
        rw [integral_const]
        simp
  have hLHS_tsum :
    ∫ ω, ∑' t, γ ^ t •
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω,
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) := by
    rw [← integral_tsum_of_summable_integral_norm hLFint hLsum]
    refine tsum_congr fun t => integral_smul (γ ^ t) _
  -- If the previous simp already unfolded the LHS series, this rewrite applies;
  -- otherwise we first put the LHS in tsum form.
  simp only [Dot.dot, Function.hPow_apply, id_eq] at hRHS_tsum ⊢
  rw [hLHS_tsum, hRHS_tsum]
  refine tsum_congr fun t => ?_
  congr 1
  have htdG : ∀ᵐ ω ∂(M θ),
      (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) =
        (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s t ω)) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) := by
    filter_upwards [htd_ae] with ω hω
    rw [hω t]
  rw [integral_congr_ae htdG]
  have hGm : Measurable fun ω => ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω :=
    (hfG t).comp hpR
  have hGscore_bd : ∀ᵐ ω ∂(M θ),
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hGbd t] with ω hG
    rw [norm_smul]
    exact mul_le_mul hG (hMs0 (s t ω) (a t ω)) (norm_nonneg _) hBG
  have hGscore : Integrable (fun ω =>
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) (M θ) :=
    Integrable.of_bound
      (hGm.stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hGscore_bd
  set hVclip : 𝒮 → ℝ := fun y => clip (M.V θ γ t y) (-BG) BG
  have hVclipm : Measurable hVclip := by
    convert hclipm.comp (hVm t)
    rfl
  have hV_eq_clip : ∀ᵐ ω ∂(M θ),
      M.V θ γ t (s t ω) = hVclip (s t ω) := by
    filter_upwards [hVbd] with ω hv
    have hlo : -BG ≤ M.V θ γ t (s t ω) := (abs_le.1 (hv t)).1
    have hhi : M.V θ γ t (s t ω) ≤ BG := (abs_le.1 (hv t)).2
    simp only [hVclip]
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have hV0score_bd : ∀ᵐ ω ∂(M θ),
      ‖M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hVbd] with ω hv
    rw [norm_smul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hv t)
      (hMs0 (s t ω) (a t ω)) (norm_nonneg _) hBG
  have hV0score : Integrable (fun ω =>
      M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) (M θ) :=
    Integrable.of_bound
      (((hVm t).comp (hs_meas t)).stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hV0score_bd
  have hsplit :
    ∫ ω, ((((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s t ω)) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) =
      ∫ ω, (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) -
      ∫ ω, (M.V θ γ t (s t ω) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) := by
    simp only [sub_smul]
    exact integral_sub hGscore hV0score
  rw [hsplit]
  have hdrop (h : 𝒮 → ℝ) (hh : Measurable h) (hC : ∀ y, ‖h y‖ ≤ BG) :
    ∫ ω, (h (s t ω) • ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) = 0 := by
    simp only [gradient]
    have hfun :
      (fun ω => h (s t ω) •
        e (fderiv ℝ (fun κ => Real.log (M.π κ (s t ω) (a t ω))) θ)) =
      fun ω => L (h (s t ω) •
        fderiv ℝ (fun κ => Real.log (M.π κ (s t ω) (a t ω))) θ) := by
      funext ω
      exact (L.map_smul (h (s t ω)) _).symm
    rw [hfun]
    have hinter : Integrable (fun ω =>
        h (s t ω) •
          fderiv ℝ (fun κ => Real.log (M.π κ (s t ω) (a t ω))) θ) (M θ) :=
      Integrable.of_bound
        ((hh.comp (hs_meas t)).stronglyMeasurable.smul
          (hφ.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
        (BG * max Ms 0) (Filter.Eventually.of_forall fun ω => by
          rw [norm_smul]
          exact mul_le_mul (hC (s t ω)) (le_trans (hMsle (s t ω) (a t ω)) (le_max_left _ _))
            (norm_nonneg _) hBG)
    have hz :
        ∫ ω, h (s t ω) •
            fderiv ℝ (fun κ => Real.log (M.π κ (s t ω) (a t ω))) θ ∂(M θ) = 0 :=
      Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
        (M := M) θ h₁ h₃ hintg hBdd h hh hC hφ hMsle t
    rw [L.integral_comp_comm (fun ω =>
        h (s t ω) •
          fderiv ℝ (fun κ => Real.log (M.π κ (s t ω) (a t ω))) θ), hz, L.map_zero]
  have hV0z :
    ∫ ω, (M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) = 0 := by
    have hclipz := hdrop hVclip hVclipm (by simpa [hVclip] using fun y => hclip_le (M.V θ γ t y))
    have hae : ∀ᵐ ω ∂(M θ),
        M.V θ γ t (s t ω) •
          ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) =
          hVclip (s t ω) •
            ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) := by
      filter_upwards [hV_eq_clip] with ω h
      rw [h]
    rw [integral_congr_ae hae, hclipz]
  rw [hV0z, sub_zero]

  have hQret :
    ∫ ω, (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) =
      ∫ ω, (M.Q θ γ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) ∂(M θ) := by
    have hret := integral_return_smul_eq_cond (M := M) (ψ := fun sₜ aₜ =>
        ∇[θ] Real.log (M.π θ sₜ aₜ)) h₀ h₁ hgradSm (fun x u => hMs0 x u) hR θ t
    refine hret.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_))
    have hq := Q_eq_expect (M := M) h₁ θ γ t (s t ω) (a t ω)
    simp [hq, Expectation.asRV, AsPathRV.path_process]
  rw [hQret]
  have hIntA_bd : ∀ᵐ ω ∂(M θ),
      ‖A θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))‖ ≤ Cl := by
    filter_upwards [hAB_ae t] with ω hA
    rw [norm_smul]
    exact mul_le_mul hA (hMs0 (s t ω) (a t ω))
      (norm_nonneg _) (mul_nonneg (by norm_num) hBG)
  have hIntA : Integrable (fun ω =>
      A θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) (M θ) :=
    Integrable.of_bound
      (((hAm t).smul hgradSm).comp_measurable
        ((hs_meas t).prodMk (ha_meas t))).aestronglyMeasurable
      Cl hIntA_bd
  have hIntV_bd : ∀ᵐ ω ∂(M θ),
      ‖M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hVbd] with ω hV
    rw [norm_smul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hV t)
      (hMs0 (s t ω) (a t ω)) (norm_nonneg _) hBG
  have hIntV : Integrable (fun ω =>
      M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) (M θ) :=
    Integrable.of_bound
      (((hVm t).comp (hs_meas t)).stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hIntV_bd
  have hfunQV :
    (fun ω => M.Q θ γ t (s t ω) (a t ω) •
      ∇[θ] Real.log (M.π θ (s t ω) (a t ω))) =
    fun ω => A θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) +
      M.V θ γ t (s t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) := by
    funext ω
    have : M.Q θ γ t (s t ω) (a t ω) =
        A θ t (s t ω) (a t ω) + M.V θ γ t (s t ω) := by
      rw [← hQeq, hAeq, sub_add_cancel]
    rw [this, add_smul]
  rw [hfunQV, integral_add hIntA hIntV]
  rw [← integral_add hIntA hIntV, ← hfunQV]
  have hMQ : ∀ᵐ ω ∂(M θ),
      M.Q θ γ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) =
      Q θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) :=
    Eventually.of_forall fun ω => by rw [hQeq]
  rw [integral_congr_ae hMQ]
  have hQ_eq_clip : ∀ᵐ ω ∂(M θ),
      Q θ t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) =
      Qclip t (s t ω) (a t ω) •
        ∇[θ] Real.log (M.π θ (s t ω) (a t ω)) := by
    filter_upwards [hQclip_ae t] with ω h
    simp only [getElem_nat_apply] at h
    rw [h]
  have hAInst :=
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) h₁ (hφAc t) (hCφc t) θ t
  simp only [getElem_nat_apply] at hAInst
  rw [integral_congr_ae hQ_eq_clip, hAInst]
  refine (integral_congr_ae (Eventually.of_forall fun y =>
      (hψπc_integral t y).symm)).trans
    (integral_map (μ := M θ) (hs_meas t).aemeasurable
      (f := ψπc t) (hinnerC_m t).aestronglyMeasurable)
end



-- created on 2026-11-11
-- updated on 2026-11-23

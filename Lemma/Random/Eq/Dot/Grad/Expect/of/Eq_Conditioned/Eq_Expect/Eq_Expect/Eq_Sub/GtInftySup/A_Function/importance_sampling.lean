import Notation.Fun
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.Differentiable_RealPreimageS.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob.All_EqWithDensity
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Instance.Probability.SinglePSpaceMeasurable
import Instance.Algebra.Module.HDiv
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Random.Traj.eq.Traj_ToDensityModel
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Syntax.Order.Sup
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 800000


/-- A σ-finite counting measure lives on a countable space. -/
private lemma countable_of_countableMeasure
  [CountableMeasure α] [MeasurableSingletonClass α] :
-- imply
  Countable α := by
-- proof
  have hσ : SigmaFinite (Measure.count : Measure α) := by
    rw [← CountableMeasure.measure_eq_count (α := α)]
    infer_instance
  obtain ⟨S⟩ := hσ.out
  refine Set.countable_univ_iff.mp ?_
  rw [← S.spanning]
  exact Set.countable_iUnion fun i =>
    (Measure.count_apply_lt_top.mp (S.finite i)).countable

/-- `π • fderiv log π = fderiv π`, including where the density vanishes. -/
private lemma smul_fderiv_log
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (hdiff : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (θ : Θ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  M.policy.prob θ x u • fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ =
    fderiv ℝ (fun κ => M.policy.prob κ x u) θ := by
-- proof
  if h : M.policy.prob θ x u = 0 then
    rw [h, zero_smul]
    exact (IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun κ => by
      rw [h]
      exact M.policy.nonneg κ x u)).symm
  else
    rw [fderiv.log ((hdiff x u) θ) h, smul_smul, mul_inv_cancel₀ h, one_smul]

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
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ (1 - γ)⁻¹ * |M.env.R| := by
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
  set BV : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hrm : ∀ k, Measurable (r k) := fun k => Measurable.of.All_Eq.fst h₁ k
  have hsm : ∀ k, Measurable (s k) := fun k => Measurable.of.All_Eq.snd.fst h₁ k
  have hpR : Measurable (fun ω i => r i ω) := Measurable.of_eval hrm
  have hfGret : ∀ k, Measurable
    (fun integ : ℕ → ℝ => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[k:]) := fun k =>
    Measurable.tsum fun j => (measurable_pi_apply (k + j)).const_mul _
  have hret_bd : ∀ᵐ ω ∂(M θ), ∀ k,
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ (fun j => r j ω)[k:])‖ ≤ BV := by
    have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hω k
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
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s k ω)| ≤ (1 - γ)⁻¹ * |M.env.R|)
  (t : ℕ) :
-- imply
  ∀ᵐ ω ∂(M θ),
    ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
      M.V θ γ (t + k) (s (t + k) ω)) =
      ∑' k, γ ^ k * r (t + k) ω - M.V θ γ t (s t ω) := by
-- proof
  filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ, hVbd] with ω hr hv
  exact tsum_td_eq (r := fun k => r (t + k) ω)
    (v := fun k => M.V θ γ (t + k) (s (t + k) ω)) h₀.1 h₀.2
    (fun k => by simpa [Real.norm_eq_abs] using hr (t + k))
    (fun k => hv (t + k))

/-- Integral against a density-policy kernel is the reference integral weighted by `π`. -/
private lemma integral_kernel
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : 𝒜 → E}
-- given
  (θ : Θ)
  (x : 𝒮) :
-- imply
  ∫ u, f u ∂(M[x] θ) =
    ∫ u, M.policy.prob θ x u • f u ∂μ.measure := by
-- proof
  have hπm : Measurable (M.policy.dens θ x) :=
    (M.policy.measurable_dens θ).comp measurable_prodMk_left
  have hker : M[x] θ =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ x) := by
    rw [DensityModel.getElem_apply, DensityPolicy.kernel, Kernel.withDensity_apply _ (M.policy.measurable_dens θ),
      Kernel.const_apply]
  rw [hker, integral_withDensity_eq_integral_toReal_smul hπm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ x u)]

/-- Importance weight `π' • (c • (∇π / π'))` equals the on-policy score `π • (c • ∇ log π)`. -/
private lemma is_weight_eq_score
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ θ' : Θ}
-- given
  (hdiff : ∀ x u, Differentiable ℝ (fun κ => M.policy.prob κ x u))
  (hvanish : ∀ x u, M.policy.prob θ' x u ≠ 0 ∨ M.policy.prob θ x u = 0)
  (x : 𝒮)
  (u : 𝒜)
  (c : ℝ) :
-- imply
  M.policy.prob θ' x u •
      (c • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u)) =
    M.policy.prob θ x u • (c • ∇[θ] Real.log (M.policy.prob θ x u)) := by
-- proof
  let e : StrongDual ℝ Θ ≃ₗᵢ[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm
  if hq : M.policy.prob θ' x u = 0 then
    have hp : M.policy.prob θ x u = 0 := (hvanish x u).resolve_left (not_ne_iff.mpr hq)
    simp [hq, hp, HDiv.hDiv]
  else
    have hgrad := smul_fderiv_log (M := M) hdiff θ x u
    calc
      _ = c • ∇[θ] (M.policy.prob θ x u) := by
        simp only [HDiv.hDiv]
        rw [smul_smul, smul_smul]
        refine congrArg (fun t => t • ∇[θ] (M.policy.prob θ x u)) ?_
        rw [mul_assoc, mul_comm c, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
      _ = c • e (fderiv ℝ (fun κ => M.policy.prob κ x u) θ) := by
        simp [e, gradient]
      _ = e (c • fderiv ℝ (fun κ => M.policy.prob κ x u) θ) := by
        rw [map_smul]
      _ = e (c • (M.policy.prob θ x u •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ)) := by
        rw [← hgrad]
      _ = e ((M.policy.prob θ x u * c) •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ) := by
        rw [smul_smul, mul_comm]
      _ = M.policy.prob θ x u • (c •
          e (fderiv ℝ (fun κ => Real.log (M.policy.prob κ x u)) θ)) := by
        rw [smul_smul, map_smul]
      _ = M.policy.prob θ x u • (c • ∇[θ] Real.log (M.policy.prob θ x u)) := by
        simp [e, gradient]

/-- On a countable alphabet, a state-action score pulls out of the discounted return. -/
private lemma integral_return_smul_eq_cond
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {ψ : 𝒮 → 𝒜 → E}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hψ : ∃ C, ∀ x u, ‖ψ x u‖ ≤ C)
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = s t ω ∧ a t = a t ω)) •
      ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  classical
  obtain ⟨Cψ, hCψ⟩ := hψ
  set G := (γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]
  set Q := fun x u =>
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s t = x ∧ a t = u)
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hGbd : ∀ᵐ ω ∂(M θ), ‖G ω‖ ≤ BG := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hr
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hr (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    have hG : G ω = ∑' k, γ ^ k * r (t + k) ω := by
      simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    rw [hG]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  change ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, Q (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[t:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  let pair : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => (s t ω, a t ω)
  have hpair : Measurable pair :=
    (Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t)
  have hQint (x : 𝒮) (u : 𝒜)
    (hpos : (M θ) (pair ⁻¹' {(x, u)}) ≠ 0) :
    Q x u = ∫ ω, G ω ∂(M θ)[|pair ⁻¹' {(x, u)}] := by
    have hmap : (M θ).map pair {(x, u)} ≠ 0 := by
      rwa [Measure.map_apply hpair (measurableSet_singleton (x, u))]
    simp only [Q, Expectation.asRV_process]
    exact Expectation.condEval_eq_integral hpR hpair hfG hmap
  have hatom : ∀ z : 𝒮 × 𝒜, MeasurableSet (pair ⁻¹' {z}) := fun z =>
    hpair (measurableSet_singleton z)
  have hmass : ∀ z : 𝒮 × 𝒜,
      ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ) = (M θ).real (pair ⁻¹' {z}) * Q z.1 z.2 := by
    intro z
    if h0 : (M θ) (pair ⁻¹' {z}) = 0 then
      rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul, Measure.restrict_eq_zero.mpr h0]
      simp
    else
      have hQ : Q z.1 z.2 = ∫ ω, G ω ∂(M θ)[|pair ⁻¹' {z}] := by
        simpa [pair] using hQint z.1 z.2 h0
      have hQsmul : Q z.1 z.2 =
          ((M θ) (pair ⁻¹' {z}))⁻¹.toReal • ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ) := by
        rw [hQ, ProbabilityTheory.cond, integral_smul_measure]
      rw [ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul] at hQsmul
      have hne : (M θ).real (pair ⁻¹' {z}) ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]
        exact ⟨h0, measure_ne_top (M θ) _⟩
      calc
        _ = (M θ).real (pair ⁻¹' {z}) *
              (((M θ).real (pair ⁻¹' {z}))⁻¹ * ∫ ω in pair ⁻¹' {z}, G ω ∂(M θ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
        _ = (M θ).real (pair ⁻¹' {z}) * Q z.1 z.2 := by
          rw [← hQsmul]
  have hpos_ae : ∀ᵐ ω ∂(M θ), (M θ) (pair ⁻¹' {pair ω}) ≠ 0 := by
    rw [ae_iff]
    have e : {ω : ℕ → ℝ × 𝒮 × 𝒜 | ¬(M θ) (pair ⁻¹' {pair ω}) ≠ 0} =
        ⋃ z ∈ {z : 𝒮 × 𝒜 | (M θ) (pair ⁻¹' {z}) = 0}, pair ⁻¹' {z} := by
      ext ω
      simp
    rw [e]
    refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun z hz => hz
  have hQbd_pos (x : 𝒮) (u : 𝒜)
    (hpos : (M θ) (pair ⁻¹' {(x, u)}) ≠ 0) :
    ‖Q x u‖ ≤ BG := by
    rw [hQint x u hpos]
    have hae : ∀ᵐ ω ∂(M θ)[|pair ⁻¹' {(x, u)}], ‖G ω‖ ≤ BG :=
      ProbabilityTheory.cond_absolutelyContinuous.ae_le hGbd
    have : IsProbabilityMeasure (M θ)[|pair ⁻¹' {(x, u)}] :=
      ProbabilityTheory.cond_isProbabilityMeasure hpos
    simpa using norm_integral_le_of_norm_le_const (μ := (M θ)[|pair ⁻¹' {(x, u)}]) hae
  have hQbd : ∀ᵐ ω ∂(M θ), ‖Q (s t ω) (a t ω)‖ ≤ BG := by
    filter_upwards [hpos_ae] with ω hpos
    simpa [pair] using hQbd_pos (s t ω) (a t ω) hpos
  have hGm : Measurable G := by
    have hfun : G = fun ω => ∑' k, γ ^ k * r (t + k) ω := by
      ext ω
      simp [G, Dot.dot, Function.hPow_apply, id_eq, Function.getSliceFrom]
    rw [hfun]
    exact Measurable.tsum fun k => (Measurable.of.All_Eq.fst h₁ (t + k)).const_mul ((γ ^ (id : ℕ → ℕ)) k)
  let F : (𝒮 × 𝒜) → (ℕ → ℝ × 𝒮 × 𝒜) → E := fun z ω =>
    (if pair ω = z then G ω else (0 : ℝ)) • ψ z.1 z.2
  let H : (𝒮 × 𝒜) → (ℕ → ℝ × 𝒮 × 𝒜) → E := fun z ω =>
    (if pair ω = z then Q z.1 z.2 else (0 : ℝ)) • ψ z.1 z.2
  have hC : ∀ x u, ‖ψ x u‖ ≤ max Cψ 0 := fun x u => (hCψ x u).trans (le_max_left _ _)
  have hFsm : ∀ z, StronglyMeasurable (F z) := by
    intro z
    have hFeq : F z = fun ω => (pair ⁻¹' {z}).indicator G ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [F, Set.indicator, h]
      else
        simp [F, Set.indicator, h]
    rw [hFeq]
    exact ((hGm.indicator (hatom z)).stronglyMeasurable).smul_const _
  have hHsm : ∀ z, StronglyMeasurable (H z) := by
    intro z
    have hHeq : H z = fun ω => (pair ⁻¹' {z}).indicator (fun _ => Q z.1 z.2) ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [H, Set.indicator, h]
      else
        simp [H, Set.indicator, h]
    rw [hHeq]
    exact (stronglyMeasurable_const.indicator (hatom z)).smul_const _
  have hFnorm : ∀ ω, ∑' z, enorm (F z ω) = enorm (G ω • ψ (s t ω) (a t ω)) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [F, pair]
    ·
      intro z hz
      simp only [F]
      rw [ite_eq_right hz.symm]
      simp
  have hHnorm : ∀ ω, ∑' z, enorm (H z ω) = enorm (Q (s t ω) (a t ω) • ψ (s t ω) (a t ω)) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [H, pair]
    ·
      intro z hz
      simp only [H]
      rw [ite_eq_right hz.symm]
      simp
  have hBd : ENNReal.ofReal (BG * max Cψ 0) * (M θ) Set.univ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (M θ) _)
  have hFtop : ∑' z, ∫⁻ ω, enorm (F z ω) ∂(M θ) ≠ ⊤ := by
    rw [← lintegral_tsum fun z => (hFsm z).aestronglyMeasurable.enorm]
    suffices ∀ᵐ ω ∂(M θ), ∑' z, enorm (F z ω) ≤ ENNReal.ofReal (BG * max Cψ 0) by
      exact ne_top_of_le_ne_top (by rwa [lintegral_const]) (lintegral_mono_ae this)
    filter_upwards [hGbd] with ω hGω
    rw [hFnorm]
    calc
      _ = enorm (G ω) * enorm (ψ (s t ω) (a t ω)) := enorm_smul _ _
      _ = ENNReal.ofReal ‖G ω‖ * ENNReal.ofReal ‖ψ (s t ω) (a t ω)‖ := by
        rw [← ofReal_norm, ← ofReal_norm]
      _ ≤ ENNReal.ofReal BG * ENNReal.ofReal (max Cψ 0) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hGω) (ENNReal.ofReal_le_ofReal (hC _ _))
      _ = ENNReal.ofReal (BG * max Cψ 0) := (ENNReal.ofReal_mul hBG).symm
  have hHtop : ∑' z, ∫⁻ ω, enorm (H z ω) ∂(M θ) ≠ ⊤ := by
    rw [← lintegral_tsum fun z => (hHsm z).aestronglyMeasurable.enorm]
    suffices ∀ᵐ ω ∂(M θ), ∑' z, enorm (H z ω) ≤ ENNReal.ofReal (BG * max Cψ 0) by
      exact ne_top_of_le_ne_top (by rwa [lintegral_const]) (lintegral_mono_ae this)
    filter_upwards [hQbd] with ω hQω
    rw [hHnorm]
    calc
      _ = enorm (Q (s t ω) (a t ω)) * enorm (ψ (s t ω) (a t ω)) := enorm_smul _ _
      _ = ENNReal.ofReal ‖Q (s t ω) (a t ω)‖ * ENNReal.ofReal ‖ψ (s t ω) (a t ω)‖ := by
        rw [← ofReal_norm, ← ofReal_norm]
      _ ≤ ENNReal.ofReal BG * ENNReal.ofReal (max Cψ 0) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hQω) (ENNReal.ofReal_le_ofReal (hC _ _))
      _ = ENNReal.ofReal (BG * max Cψ 0) := (ENNReal.ofReal_mul hBG).symm
  have hsumG : ∀ ω, ∑' z, F z ω = G ω • ψ (s t ω) (a t ω) := by
    intro ω
    simp [F, pair]
  have hsumQ : ∀ ω, ∑' z, H z ω = Q (s t ω) (a t ω) • ψ (s t ω) (a t ω) := by
    intro ω
    rw [tsum_eq_single (pair ω)]
    · simp [H, pair]
    ·
      intro z hz
      simp only [H]
      rw [ite_eq_right hz.symm]
      simp
  have htermF : ∀ z, ∫ ω, F z ω ∂(M θ) =
      (M θ).real (pair ⁻¹' {z}) • (Q z.1 z.2 • ψ z.1 z.2) := by
    intro z
    have hfun : (fun ω => (if pair ω = z then G ω else (0 : ℝ)) • ψ z.1 z.2) =
        fun ω => (pair ⁻¹' {z}).indicator G ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [Set.indicator, h]
      else
        simp [Set.indicator, h]
    simp only [F]
    rw [hfun, integral_smul_const, integral_indicator (hatom z), hmass z, mul_smul]
  have htermH : ∀ z, ∫ ω, H z ω ∂(M θ) =
      (M θ).real (pair ⁻¹' {z}) • (Q z.1 z.2 • ψ z.1 z.2) := by
    intro z
    have hfun : (fun ω => (if pair ω = z then Q z.1 z.2 else (0 : ℝ)) • ψ z.1 z.2) =
        fun ω => (pair ⁻¹' {z}).indicator (fun _ => Q z.1 z.2) ω • ψ z.1 z.2 := by
      ext ω
      if h : pair ω = z then
        simp [Set.indicator, h]
      else
        simp [Set.indicator, h]
    simp only [H]
    rw [hfun, integral_smul_const, integral_indicator_const _ (hatom z), smul_eq_mul, mul_smul]
  rw [integral_congr_ae (ae_of_all _ fun ω => (hsumG ω).symm),
    integral_tsum (fun z => (hFsm z).aestronglyMeasurable) hFtop,
    integral_congr_ae (ae_of_all _ fun ω => (hsumQ ω).symm),
    integral_tsum (fun z => (hHsm z).aestronglyMeasurable) hHtop]
  simp_rw [htermF, htermH]

/-- The proposal kernel's counting density is the policy probability. -/
private lemma kernel_pmf
  [MeasurableSpace 𝒮] [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ' : Θ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  ((M[x] θ').prob (id : 𝒜 → 𝒜) u).toReal = M.policy.prob θ' x u := by
-- proof
  have hden :
    (M[x] θ').prob (id : 𝒜 → 𝒜) u = (M[x] θ') {u} := by
    rw [Measure.prob, Measure.map_id, CountableMeasure.measure_eq_count]
    exact EqRnDeriv_Count u
  rw [hden]
  have hker : M[x] θ' =
      (ReferenceMeasure.measure : Measure 𝒜).withDensity (M.policy.dens θ' x) := by
    rw [DensityModel.getElem_apply, DensityPolicy.kernel, Kernel.withDensity_apply _ (M.policy.measurable_dens θ'),
      Kernel.const_apply]
  rw [hker, MeasureTheory.withDensity_apply _ (measurableSet_singleton u)]
  have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
    CountableMeasure.measure_eq_count
  rw [hμ, lintegral_singleton, count_singleton, mul_one]
  simp [DensityPolicy.dens, ENNReal.toReal_ofReal (M.policy.nonneg θ' x u)]

/-- Almost every visited state is reachable, on a countable alphabet. -/
private lemma ae_real_preimage_ne_zero
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
-- given
  (hs : ∀ t, Measurable (s t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ t, (M θ).real (s t ⁻¹' {s t ω}) ≠ 0 := by
-- proof
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  have e : {ω : ℕ → ℝ × 𝒮 × 𝒜 | ¬(M θ).real (s t ⁻¹' {s t ω}) ≠ 0} =
      ⋃ y ∈ {y : 𝒮 | (M θ).real (s t ⁻¹' {y}) = 0}, s t ⁻¹' {y} := by
    ext ω
    simp
  rw [e]
  refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun y hy => ?_
  have hy0 : (M θ).real (s t ⁻¹' {y}) = 0 := hy
  have htop : (M θ) (s t ⁻¹' {y}) ≠ ⊤ := measure_ne_top _ _
  have hmeas : MeasurableSet (s t ⁻¹' {y}) := hs t (measurableSet_singleton _)
  have hreal : ((M θ) (s t ⁻¹' {y})).toReal = 0 := by
    rwa [measureReal_def] at hy0
  rw [ENNReal.toReal_eq_zero_iff] at hreal
  exact (hreal.resolve_right htop)

/-- At a reachable state, the trajectory conditional is the policy probability. -/
private lemma condProb_eq_ofReal_policy
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (hP : SinglePSpace (M θ) (a t, s t))
  (hpos : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : 𝒜) :
-- imply
  ((M θ).condProb (a t, s t) (u, x)).toReal = M.policy.prob θ x u := by
-- proof
  classical
  have hAS : (ReferenceMeasure.measure : Measure (𝒜 × 𝒮)) = Measure.count := by
    rw [CountableMeasure.measure_eq_count]
  have hxy : Measurable (a t, s t) :=
    (Random.Measurable.of.All_Eq.snd.snd h_all t).prodMk
      (Random.Measurable.of.All_Eq.snd.fst h_all t)
  have hnum : (M θ).prob (a t, s t) (u, x) =
      (M θ) (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := by
    unfold Measure.prob
    rw [hAS, EqRnDeriv_Count, Measure.map_apply hxy (measurableSet_singleton _)]
    congr 1
    ext ω
    simp [JointRandomSymbol, and_comm]
  have hden :
    ((M θ).map (fun ω => ((a t, s t) ω).2)).rnDeriv ReferenceMeasure.measure x =
      (M θ) (s t ⁻¹' {x}) := by
    have hsnd : (fun ω => ((a t, s t) ω).2) = s t := rfl
    rw [hsnd, CountableMeasure.measure_eq_count (α := 𝒮), EqRnDeriv_Count]
    exact Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h_all t)
      (measurableSet_singleton _)
  have hφ :
    StronglyMeasurable (Function.uncurry fun (y : 𝒮) (v : 𝒜) =>
      if (y, v) = (x, u) then (1 : ℝ) else 0) :=
    StronglyMeasurable.of_discrete
  have hC : ∀ y v, ‖(if (y, v) = (x, u) then (1 : ℝ) else 0)‖ ≤ 1 := by
    intro y v
    split_ifs <;> simp
  have hinter :=
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) (φ := fun y v => if (y, v) = (x, u) then (1 : ℝ) else 0)
      (C := 1) h_all hφ hC θ t
  have hL : ∫ ω, (if (s t ω, a t ω) = (x, u) then (1 : ℝ) else 0) ∂(M θ) =
      (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) := by
    have hset : MeasurableSet (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) :=
      ((Random.Measurable.of.All_Eq.snd.fst h_all t) (measurableSet_singleton _)).inter
        ((Random.Measurable.of.All_Eq.snd.snd h_all t) (measurableSet_singleton _))
    have hfun :
      (fun ω => if (s t ω, a t ω) = (x, u) then (1 : ℝ) else 0) =
        (s t ⁻¹' {x} ∩ a t ⁻¹' {u}).indicator fun _ => (1 : ℝ) := by
      ext ω
      simp [Set.indicator]
    rw [hfun, integral_indicator_const _ hset, smul_eq_mul, mul_one]
  have hR : ∫ y, (∫ v, M.policy.prob θ y v •
        (if (y, v) = (x, u) then (1 : ℝ) else 0) ∂ReferenceMeasure.measure)
      ∂((M θ).map (s t)) =
      (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u := by
    have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
      CountableMeasure.measure_eq_count
    have hintery : ∀ y,
        ∫ v, M.policy.prob θ y v • (if (y, v) = (x, u) then (1 : ℝ) else 0)
          ∂ReferenceMeasure.measure =
          if y = x then M.policy.prob θ x u else 0 := by
      intro y
      rw [hμ]
      have hfun :
        (fun v => M.policy.prob θ y v • (if (y, v) = (x, u) then (1 : ℝ) else 0)) =
          fun v => if y = x ∧ v = u then M.policy.prob θ y v else 0 := by
        ext v
        if h : (y, v) = (x, u) then
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          simp
        else
          have hne' : ¬(y = x ∧ v = u) := fun ⟨hy, hv⟩ => h (Prod.ext hy hv)
          simp [h, smul_eq_mul, hne']
      rw [hfun]
      if hy : y = x then
        have hfun' :
          (fun v => if y = x ∧ v = u then M.policy.prob θ y v else 0) =
            ({u} : Set 𝒜).indicator fun _ => M.policy.prob θ x u := by
          ext v
          if hv : v = u then
            simp [Set.indicator, hy, hv]
          else
            simp [Set.indicator, hy, hv]
        rw [hfun', integral_indicator_const _ (measurableSet_singleton u), smul_eq_mul,
          measureReal_def, count_singleton, ENNReal.toReal_one, one_mul]
        simp [hy]
      else
        have hfun' :
          (fun v => if y = x ∧ v = u then M.policy.prob θ y v else 0) = 0 := by
          ext v
          simp [hy]
        rw [hfun']
        simp [hy]
    simp_rw [hintery]
    have hfun :
      (fun y => if y = x then M.policy.prob θ x u else (0 : ℝ)) =
        ({x} : Set 𝒮).indicator fun _ => M.policy.prob θ x u := by
      ext y
      simp [Set.indicator]
    rw [hfun, integral_indicator_const _ (measurableSet_singleton x), smul_eq_mul,
      measureReal_def, Measure.map_apply (Random.Measurable.of.All_Eq.snd.fst h_all t)
        (measurableSet_singleton x), ← measureReal_def, mul_comm]
  have hxu : (M θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) =
      (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u := by
    rw [← hL, hinter, hR]
  change ((M θ).prob (a t, s t) (u, x) /
      ((M θ).map (fun ω => ((a t, s t) ω).2)).rnDeriv ReferenceMeasure.measure x).toReal = _
  rw [hnum, hden]
  have hne : (M θ) (s t ⁻¹' {x}) ≠ 0 := by
    have htop : (M θ) (s t ⁻¹' {x}) ≠ ⊤ := measure_ne_top _ _
    rw [measureReal_def] at hpos
    exact (ENNReal.toReal_ne_zero.mp hpos).1
  have htop : (M θ) (s t ⁻¹' {x}) ≠ ⊤ := measure_ne_top _ _
  rw [← ofReal_measureReal (measure_ne_top (M θ) (s t ⁻¹' {x} ∩ a t ⁻¹' {u}))]
  rw [hxu, ENNReal.ofReal_mul measureReal_nonneg]
  simp only [measureReal_def]
  rw [ENNReal.ofReal_toReal htop, mul_comm ((M θ) (s t ⁻¹' {x})),
    ENNReal.mul_div_cancel_right hne htop,
    ENNReal.toReal_ofReal (M.policy.nonneg θ x u)]

private lemma joint_ne_zero_of_state_ne_zero
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
  {u : 𝒜}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (hP : SinglePSpace (M θ) (a t, s t))
  (hpos : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (hπ : M.policy.prob θ x u ≠ 0) :
-- imply
  (M θ) (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) ≠ 0 := by
-- proof
  have hcp := condProb_eq_ofReal_policy (M := M) h_all hP hpos u
  have hcp_ne : (M θ).condProb (a t, s t) (u, x) ≠ 0 := by
    intro hz
    have : ((M θ).condProb (a t, s t) (u, x)).toReal = 0 := by simp [hz]
    exact hπ (hcp.symm.trans this)
  intro h0
  apply hcp_ne
  unfold Measure.condProb
  have hnum : (M θ).prob (a t, s t) (u, x) = 0 := by
    have hAS : (ReferenceMeasure.measure : Measure (𝒜 × 𝒮)) = Measure.count := by
      rw [CountableMeasure.measure_eq_count]
    have hxy : Measurable (a t, s t) :=
      (Measurable.of.All_Eq.snd.snd h_all t).prodMk
        (Measurable.of.All_Eq.snd.fst h_all t)
    unfold Measure.prob
    rw [hAS, EqRnDeriv_Count, Measure.map_apply hxy (measurableSet_singleton _)]
    convert h0
    ext ω
    simp [JointRandomSymbol, and_comm]
  simp [hnum]

/-- Transition mass at a singleton is at most one. -/
private lemma trans_real_le_one
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (z : 𝒮 × 𝒜)
  (x : 𝒮) :
-- imply
  0 ≤ (M.env.trans z).real {x} ∧ (M.env.trans z).real {x} ≤ 1 := by
-- proof
  have := M.env.trans_markov
  have : IsProbabilityMeasure (M.env.trans z) := inferInstance
  refine ⟨measureReal_nonneg, ?_⟩
  exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ

/-- The policy is integrable against the action reference measure. -/
private lemma integrable_policy_prob
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y : 𝒮) :
-- imply
  Integrable (M.policy.prob θ y) μ.measure := by
-- proof
  by_contra h
  apply one_ne_zero ((M.policy.integral_eq_one θ y).symm.trans (integral_undef h))

/-- Occupancy of a fixed state sums to one. -/
private lemma tsum_state_mass_eq_one
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  ∑' y, (M θ).real (s t ⁻¹' {y}) = 1 ∧
    Summable fun y => (M θ).real (s t ⁻¹' {y}) := by
-- proof
  have hs : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h_all t
  have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
  have hinter : Integrable (fun _ : 𝒮 => (1 : ℝ)) ((M θ).map (s t)) := integrable_const 1
  have htsum : ∑' y, ((M θ).map (s t)).real {y} = 1 := by
    have h := integral_countable (μ := (M θ).map (s t)) hinter
    simp only [smul_eq_mul, mul_one] at h
    apply h.symm.trans
    simp [integral_const, probReal_univ]
  have hmass : (fun y => ((M θ).map (s t)).real {y}) =
      fun y => (M θ).real (s t ⁻¹' {y}) := by
    ext y
    rw [measureReal_def, Measure.map_apply hs (measurableSet_singleton y), ← measureReal_def]
  rw [hmass] at htsum
  refine ⟨htsum, ?_⟩
  by_contra hns
  exact one_ne_zero (htsum.symm.trans (tsum_eq_zero_of_not_summable hns))

/-- The occupancy kernel mass is a probability-weighted transition mass in [0, 1]. -/
private lemma kernel_mass_mem_Icc
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (y x : 𝒮) :
-- imply
  let p := ∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
    ∂(ReferenceMeasure.measure : Measure 𝒜)
  0 ≤ p ∧ p ≤ 1 ∧
    Integrable (fun u => M.policy.prob θ y u * (M.env.trans (y, u)).real {x})
      (ReferenceMeasure.measure : Measure 𝒜) := by
-- proof
  intro p
  have hπint := integrable_policy_prob (M := M) θ y
  have hle : ∀ u,
      ‖M.policy.prob θ y u * (M.env.trans (y, u)).real {x}‖ ≤ M.policy.prob θ y u := by
    intro u
    have ⟨hT0, hT1⟩ := trans_real_le_one (M := M) (y, u) x
    have hπ0 := M.policy.nonneg θ y u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hπ0, abs_of_nonneg hT0]
    exact mul_le_of_le_one_right hπ0 hT1
  have hmeas : AEStronglyMeasurable
    (fun u => M.policy.prob θ y u * (M.env.trans (y, u)).real {x})
    (ReferenceMeasure.measure : Measure 𝒜) :=
    (Measurable.mul
      ((M.policy.measurable_prob θ).comp (measurable_prodMk_left (x := y)))
      (((M.env.trans.measurable_coe (measurableSet_singleton x)).ennreal_toReal).comp
        (measurable_prodMk_left (x := y)))).aestronglyMeasurable
  have hint : Integrable
    (fun u => M.policy.prob θ y u * (M.env.trans (y, u)).real {x})
    (ReferenceMeasure.measure : Measure 𝒜) :=
    Integrable.mono' hπint hmeas (Filter.Eventually.of_forall hle)
  have hnn : 0 ≤ p :=
    integral_nonneg fun u =>
      mul_nonneg (M.policy.nonneg θ y u) (trans_real_le_one (M := M) (y, u) x).1
  refine ⟨hnn, ?_, hint⟩
  calc
    _ ≤ ∫ u, M.policy.prob θ y u ∂(ReferenceMeasure.measure : Measure 𝒜) :=
      integral_mono hint hπint fun u =>
        mul_le_of_le_one_right (M.policy.nonneg θ y u)
          (trans_real_le_one (M := M) (y, u) x).2
    _ = 1 := M.policy.integral_eq_one θ y

/-- The occupancy kernel mass depends continuously on the parameter. -/
private lemma continuousAt_kernel_mass
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [μ : CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (hdiff : ∀ y u, Differentiable ℝ (fun κ => M.policy.prob κ y u))
  (y x : 𝒮)
  (θ : Θ) :
-- imply
  ContinuousAt (fun κ =>
    ∫ u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}
      ∂μ.measure) θ := by
-- proof
  classical
  set p : Θ → ℝ := fun κ =>
    ∫ u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}
      ∂(ReferenceMeasure.measure : Measure 𝒜)
  have hμ : (ReferenceMeasure.measure : Measure 𝒜) = Measure.count :=
    CountableMeasure.measure_eq_count
  have hp : p = fun κ =>
      ∑' u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} := by
    ext κ
    have hint := (kernel_mass_mem_Icc (M := M) κ y x).2.2
    have h := integral_countable (μ := (ReferenceMeasure.measure : Measure 𝒜)) hint
    refine h.trans (tsum_congr fun u => ?_)
    have : (ReferenceMeasure.measure : Measure 𝒜).real {u} = 1 := by
      rw [hμ, measureReal_def, count_singleton, ENNReal.toReal_one]
    rw [smul_eq_mul, this, one_mul]
  rw [hp]
  have hπsum : ∀ κ, ∑' u, M.policy.prob κ y u = 1 ∧
      Summable fun u => M.policy.prob κ y u := by
    intro κ
    have hint := integrable_policy_prob (M := M) κ y
    have h := integral_countable (μ := (ReferenceMeasure.measure : Measure 𝒜)) hint
    have h1 : ∑' u, (ReferenceMeasure.measure : Measure 𝒜).real {u} * M.policy.prob κ y u = 1 := by
      simpa [smul_eq_mul] using h.symm.trans (M.policy.integral_eq_one κ y)
    have hmass : (fun u => (ReferenceMeasure.measure : Measure 𝒜).real {u} * M.policy.prob κ y u) =
        fun u => M.policy.prob κ y u := by
      ext u
      have : (ReferenceMeasure.measure : Measure 𝒜).real {u} = 1 := by
        rw [hμ, measureReal_def, count_singleton, ENNReal.toReal_one]
      rw [this, one_mul]
    rw [hmass] at h1
    refine ⟨h1, ?_⟩
    by_contra hns
    exact one_ne_zero (h1.symm.trans (tsum_eq_zero_of_not_summable hns))
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hε6 : 0 < ε / 6 := by positivity
  have hsumθ := (hπsum θ).2
  obtain ⟨F, hF⟩ : ∃ F : Finset 𝒜,
      ∑' u : { u // u ∉ F }, M.policy.prob θ y u < ε / 6 := by
    have hsplit : ∀ F, ∑' u : { u // u ∉ F }, M.policy.prob θ y u =
        ∑' u, M.policy.prob θ y u - ∑ u ∈ F, M.policy.prob θ y u := fun F => by
      linarith [hsumθ.sum_add_tsum_subtype_compl F]
    have htend : Tendsto (fun F : Finset 𝒜 =>
        ∑' u : { u // u ∉ F }, M.policy.prob θ y u) atTop (nhds 0) := by
      have hconst : Tendsto (fun F : Finset 𝒜 =>
          ∑' u, M.policy.prob θ y u - ∑ u ∈ F, M.policy.prob θ y u)
          atTop (nhds (∑' u, M.policy.prob θ y u - ∑' u, M.policy.prob θ y u)) :=
        tendsto_const_nhds.sub hsumθ.hasSum
      simpa [hsplit, sub_self] using hconst
    obtain ⟨F, hFF⟩ := Metric.tendsto_atTop.mp htend (ε / 6) hε6
    refine ⟨F, ?_⟩
    have habs : |∑' u : { u // u ∉ F }, M.policy.prob θ y u - 0| < ε / 6 := hFF F le_rfl
    have hnn : 0 ≤ ∑' u : { u // u ∉ F }, M.policy.prob θ y u :=
      tsum_nonneg fun u => M.policy.nonneg θ y u.1
    simpa [sub_zero, abs_of_nonneg hnn] using habs
  have hcontπ : ∀ u, ContinuousAt (fun κ => M.policy.prob κ y u) θ :=
    fun u => ((hdiff y u) θ).continuousAt
  have hcontF : ContinuousAt (fun κ => ∑ u ∈ F, M.policy.prob κ y u) θ :=
    tendsto_finsetSum F (fun u _ => hcontπ u)
  have hcontg : ∀ u, ContinuousAt
    (fun κ => M.policy.prob κ y u * (M.env.trans (y, u)).real {x}) θ :=
    fun u => (hcontπ u).mul continuousAt_const
  have hcontFg : ContinuousAt
    (fun κ => ∑ u ∈ F, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}) θ :=
    tendsto_finsetSum F (fun u _ => hcontg u)
  have hnearπ : ∀ᶠ κ in 𝓝 θ, |∑ u ∈ F, M.policy.prob κ y u - ∑ u ∈ F, M.policy.prob θ y u| < ε / 6 :=
    Metric.tendsto_nhds.mp hcontF (ε / 6) hε6
  have hnearg : ∀ᶠ κ in 𝓝 θ,
      |∑ u ∈ F, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
        ∑ u ∈ F, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| < ε / 3 :=
    Metric.tendsto_nhds.mp hcontFg (ε / 3) (by positivity)
  filter_upwards [hnearπ, hnearg] with κ hκπ hκg
  have hsummκ := (hπsum κ).2
  have hsplit : ∀ κ' (hsm : Summable fun u => M.policy.prob κ' y u),
      ∑' u, M.policy.prob κ' y u * (M.env.trans (y, u)).real {x} =
        ∑ u ∈ F, M.policy.prob κ' y u * (M.env.trans (y, u)).real {x} +
          ∑' u : { u // u ∉ F }, M.policy.prob κ' y u * (M.env.trans (y, u)).real {x} := by
    intro κ' hsm
    have hsmg : Summable fun u =>
        M.policy.prob κ' y u * (M.env.trans (y, u)).real {x} := by
      refine Summable.of_nonneg_of_le
        (fun u => mul_nonneg (M.policy.nonneg κ' y u) (trans_real_le_one (M := M) (y, u) x).1)
        (fun u => mul_le_of_le_one_right (M.policy.nonneg κ' y u)
          (trans_real_le_one (M := M) (y, u) x).2)
        hsm
    simpa using (hsmg.sum_add_tsum_subtype_compl F).symm
  have htailθ :
    |∑' u : { u // u ∉ F }, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| ≤
      ∑' u : { u // u ∉ F }, M.policy.prob θ y u := by
    have hnn : 0 ≤ ∑' u : { u // u ∉ F },
        M.policy.prob θ y u * (M.env.trans (y, u)).real {x} :=
      tsum_nonneg fun u =>
        mul_nonneg (M.policy.nonneg θ y u.1) (trans_real_le_one (M := M) (y, u.1) x).1
    rw [abs_of_nonneg hnn]
    refine Summable.tsum_le_tsum ?_ ?_ (hsumθ.subtype _)
    ·
      intro u
      exact mul_le_of_le_one_right (M.policy.nonneg θ y u.1)
        (trans_real_le_one (M := M) (y, u.1) x).2
    · exact (Summable.of_nonneg_of_le
        (fun u => mul_nonneg (M.policy.nonneg θ y u.1) (trans_real_le_one (M := M) (y, u.1) x).1)
        (fun u => mul_le_of_le_one_right (M.policy.nonneg θ y u.1)
          (trans_real_le_one (M := M) (y, u.1) x).2)
        (hsumθ.subtype _))
  have htailθ' : |∑' u : { u // u ∉ F },
      M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| < ε / 6 :=
    lt_of_le_of_lt htailθ hF
  have htailπκ : ∑' u : { u // u ∉ F }, M.policy.prob κ y u < ε / 3 := by
    have hsplitπ := (hsummκ.sum_add_tsum_subtype_compl F).symm
    have h1κ : ∑' u, M.policy.prob κ y u = 1 := (hπsum κ).1
    have h1θ : ∑' u, M.policy.prob θ y u = 1 := (hπsum θ).1
    have hsplitθ := (hsumθ.sum_add_tsum_subtype_compl F).symm
    have htailκeq : ∑' u : { u // u ∉ F }, M.policy.prob κ y u =
        1 - ∑ u ∈ F, M.policy.prob κ y u := by
      linarith
    have htailθeq : ∑' u : { u // u ∉ F }, M.policy.prob θ y u =
        1 - ∑ u ∈ F, M.policy.prob θ y u := by
      linarith
    have : |∑' u : { u // u ∉ F }, M.policy.prob κ y u -
        ∑' u : { u // u ∉ F }, M.policy.prob θ y u| =
        |∑ u ∈ F, M.policy.prob θ y u - ∑ u ∈ F, M.policy.prob κ y u| := by
      rw [htailκeq, htailθeq]
      ring_nf
    have : |∑' u : { u // u ∉ F }, M.policy.prob κ y u -
        ∑' u : { u // u ∉ F }, M.policy.prob θ y u| < ε / 6 := by
      rwa [this, abs_sub_comm]
    have hnn : 0 ≤ ∑' u : { u // u ∉ F }, M.policy.prob κ y u :=
      tsum_nonneg fun u => M.policy.nonneg κ y u.1
    have hpos : ∑' u : { u // u ∉ F }, M.policy.prob κ y u < ε / 6 + ε / 6 := by
      have := (abs_sub_lt_iff.mp this).1
      linarith [hF]
    linarith
  have htailκ :
    |∑' u : { u // u ∉ F }, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}| < ε / 3 := by
    have hnn : 0 ≤ ∑' u : { u // u ∉ F },
        M.policy.prob κ y u * (M.env.trans (y, u)).real {x} :=
      tsum_nonneg fun u =>
        mul_nonneg (M.policy.nonneg κ y u.1) (trans_real_le_one (M := M) (y, u.1) x).1
    rw [abs_of_nonneg hnn]
    refine lt_of_le_of_lt ?_ htailπκ
    refine Summable.tsum_le_tsum ?_ ?_ (hsummκ.subtype _)
    ·
      intro u
      exact mul_le_of_le_one_right (M.policy.nonneg κ y u.1)
        (trans_real_le_one (M := M) (y, u.1) x).2
    · exact (Summable.of_nonneg_of_le
        (fun u => mul_nonneg (M.policy.nonneg κ y u.1) (trans_real_le_one (M := M) (y, u.1) x).1)
        (fun u => mul_le_of_le_one_right (M.policy.nonneg κ y u.1)
          (trans_real_le_one (M := M) (y, u.1) x).2)
        (hsummκ.subtype _))
  have : |∑' u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
      ∑' u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| < ε := by
    rw [hsplit κ hsummκ, hsplit θ hsumθ]
    calc
      _ = |(∑ u ∈ F, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
            ∑ u ∈ F, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}) +
          (∑' u : { u // u ∉ F }, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
            ∑' u : { u // u ∉ F }, M.policy.prob θ y u * (M.env.trans (y, u)).real {x})| := by
        ring_nf
      _ ≤ |∑ u ∈ F, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
            ∑ u ∈ F, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| +
          |∑' u : { u // u ∉ F }, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}| +
          |∑' u : { u // u ∉ F }, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}| := by
        set A := ∑ u ∈ F, M.policy.prob κ y u * (M.env.trans (y, u)).real {x} -
          ∑ u ∈ F, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        set B := ∑' u : { u // u ∉ F }, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}
        set C := ∑' u : { u // u ∉ F }, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        have h1 : |A + (B - C)| ≤ |A| + |B - C| := by
          simpa [Real.norm_eq_abs] using norm_add_le A (B - C)
        have h2 : |B - C| ≤ |B| + |C| := by
          simpa [Real.norm_eq_abs] using norm_sub_le B C
        linarith
      _ < ε / 3 + ε / 3 + ε / 6 := by
        linarith [hκg, htailκ, htailθ']
      _ < ε := by linarith
  simpa [Real.dist_eq] using this

/-- Occupancy of the next state is the occupancy-weighted kernel mass. -/
private lemma real_preimage_succ
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [μ : CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : 𝒮) :
-- imply
  (M θ).real (s (t + 1) ⁻¹' {x}) =
    ∑' y, (M θ).real (s t ⁻¹' {y}) *
      (∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        ∂μ.measure) := by
-- proof
  have hs : Measurable (s (t + 1)) := Random.Measurable.of.All_Eq.snd.fst h_all (t + 1)
  have hst : Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h_all t
  have hpair : Measurable fun ω => (s t ω, a t ω) :=
    (Random.Measurable.of.All_Eq.snd.fst h_all t).prodMk
      (Random.Measurable.of.All_Eq.snd.snd h_all t)
  have hmap := Map.eq.Trans.of.All_Eq_Joint.All_EqWithDensity (M := M) h_all θ t
  have hbind :
    ((M.env.trans ∘ₘ (M θ).map (fun ω => (s t ω, a t ω))) {x}).toReal =
      (∫⁻ z, M.env.trans z {x} ∂((M θ).map (fun ω => (s t ω, a t ω)))).toReal := by
    rw [Measure.bind_apply (measurableSet_singleton x) (Kernel.aemeasurable M.env.trans)]
  have hTle : ∀ z, ‖(M.env.trans z).real {x}‖ ≤ 1 := fun z => by
    have ⟨h0, h1⟩ := trans_real_le_one (M := M) z x
    rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hTmeas : AEStronglyMeasurable (fun z => (M.env.trans z).real {x})
      ((M θ).map (fun ω => (s t ω, a t ω))) :=
    (M.env.trans.measurable_coe (measurableSet_singleton x)).ennreal_toReal.aestronglyMeasurable
  have : IsProbabilityMeasure ((M θ).map (fun ω => (s t ω, a t ω))) :=
    inferInstance
  have hTint : Integrable (fun z => (M.env.trans z).real {x})
      ((M θ).map (fun ω => (s t ω, a t ω))) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hTmeas (Filter.Eventually.of_forall hTle)
  have hlin :
    (∫⁻ z, M.env.trans z {x} ∂((M θ).map (fun ω => (s t ω, a t ω)))).toReal =
      ∫ z, (M.env.trans z).real {x} ∂((M θ).map (fun ω => (s t ω, a t ω))) := by
    have hcongr : (fun z => M.env.trans z {x}) =
        fun z => ENNReal.ofReal ((M.env.trans z).real {x}) := by
      ext z
      have := M.env.trans_markov
      have : IsProbabilityMeasure (M.env.trans z) := inferInstance
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hTint
        (Filter.Eventually.of_forall fun _ => measureReal_nonneg),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => measureReal_nonneg)]
  have hsa :
    ∫ z, (M.env.trans z).real {x} ∂((M θ).map (fun ω => (s t ω, a t ω))) =
      ∫ ω, (M.env.trans (s t ω, a t ω)).real {x} ∂(M θ) :=
    integral_map hpair.aemeasurable hTint.aestronglyMeasurable
  have hφ : StronglyMeasurable
    (Function.uncurry fun (y : 𝒮) (u : 𝒜) => (M.env.trans (y, u)).real {x}) :=
    StronglyMeasurable.of_discrete
  have hinter :=
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) (φ := fun y u => (M.env.trans (y, u)).real {x}) (C := 1)
      h_all hφ (fun y u => hTle (y, u)) θ t
  have hsmul :
    ∫ y, (∫ u, M.policy.prob θ y u • (M.env.trans (y, u)).real {x}
        ∂(ReferenceMeasure.measure : Measure 𝒜)) ∂((M θ).map (s t)) =
      ∫ y, (∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        ∂(ReferenceMeasure.measure : Measure 𝒜)) ∂((M θ).map (s t)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y =>
      integral_congr_ae (Filter.Eventually.of_forall fun u => smul_eq_mul _ _))
  have : IsProbabilityMeasure ((M θ).map (s t)) := inferInstance
  have hinterg :
    Integrable (fun y =>
      ∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        ∂(ReferenceMeasure.measure : Measure 𝒜)) ((M θ).map (s t)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      StronglyMeasurable.of_discrete.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h := kernel_mass_mem_Icc (M := M) θ y x
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    apply h.2.1
  have htsum :
    ∫ y, (∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
        ∂(ReferenceMeasure.measure : Measure 𝒜)) ∂((M θ).map (s t)) =
      ∑' y, (M θ).real (s t ⁻¹' {y}) *
        (∫ u, M.policy.prob θ y u * (M.env.trans (y, u)).real {x}
          ∂(ReferenceMeasure.measure : Measure 𝒜)) := by
    have h := integral_countable (μ := (M θ).map (s t)) hinterg
    refine h.trans (tsum_congr fun y => ?_)
    rw [smul_eq_mul, measureReal_def, Measure.map_apply hst (measurableSet_singleton y),
      ← measureReal_def]
  rw [measureReal_def, ← Measure.map_apply hs (measurableSet_singleton x), hmap]
  change ((M.env.trans ∘ₘ (M θ).map (fun ω => (s t ω, a t ω))) {x}).toReal = _
  rw [hbind, hlin, hsa, hinter, hsmul, htsum]

/-- Occupancy of a fixed state depends continuously on the parameter. -/
private lemma continuousAt_state_mass
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (hdiff : ∀ y u, Differentiable ℝ (fun κ => M.policy.prob κ y u))
  (t : ℕ)
  (x : 𝒮)
  (θ : Θ) :
-- imply
  ContinuousAt (fun κ => (M κ).real (s t ⁻¹' {x})) θ := by
-- proof
  classical
  induction t generalizing x with
  | zero =>
    have hmap : ∀ κ, (M κ).map (s 0) = M.env.init :=
      fun κ => Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity (M := M) h_all κ
    have hs : Measurable (s 0) := Random.Measurable.of.All_Eq.snd.fst h_all 0
    have hfun : (fun κ => (M κ).real (s 0 ⁻¹' {x})) = fun _ => M.env.init.real {x} := by
      ext κ
      rw [measureReal_def, ← Measure.map_apply hs (measurableSet_singleton x),
        ← measureReal_def, hmap]
    rw [hfun]
    apply continuousAt_const
  | succ t ih =>
    have hform : (fun κ => (M κ).real (s (t + 1) ⁻¹' {x})) =
        fun κ => ∑' y, (M κ).real (s t ⁻¹' {y}) *
          (∫ u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}
            ∂(ReferenceMeasure.measure : Measure 𝒜)) :=
      funext fun κ => real_preimage_succ (M := M) h_all κ t x
    rw [hform]
    set p : Θ → 𝒮 → ℝ := fun κ y =>
      ∫ u, M.policy.prob κ y u * (M.env.trans (y, u)).real {x}
        ∂(ReferenceMeasure.measure : Measure 𝒜)
    change ContinuousAt (fun κ => ∑' y, (M κ).real (s t ⁻¹' {y}) * p κ y) θ
    have hpIcc : ∀ κ y, 0 ≤ p κ y ∧ p κ y ≤ 1 := fun κ y =>
      ⟨(kernel_mass_mem_Icc (M := M) κ y x).1, (kernel_mass_mem_Icc (M := M) κ y x).2.1⟩
    have hcontp : ∀ y, ContinuousAt (fun κ => p κ y) θ :=
      fun y => continuousAt_kernel_mass (M := M) hdiff y x θ
    have hcontm : ∀ y, ContinuousAt (fun κ => (M κ).real (s t ⁻¹' {y})) θ :=
      fun y => ih y
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    have hε6 : 0 < ε / 6 := by positivity
    have hsumθ := (tsum_state_mass_eq_one (M := M) h_all θ t).2
    obtain ⟨F, hF⟩ : ∃ F : Finset 𝒮,
        ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) < ε / 6 := by
      have hsplit : ∀ F, ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) =
          ∑' y, (M θ).real (s t ⁻¹' {y}) - ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) :=
        fun F => by linarith [hsumθ.sum_add_tsum_subtype_compl F]
      have htend : Tendsto (fun F : Finset 𝒮 =>
          ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1})) atTop (nhds 0) := by
        have hconst : Tendsto (fun F : Finset 𝒮 =>
            ∑' y, (M θ).real (s t ⁻¹' {y}) - ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}))
            atTop (nhds (∑' y, (M θ).real (s t ⁻¹' {y}) - ∑' y, (M θ).real (s t ⁻¹' {y}))) :=
          tendsto_const_nhds.sub hsumθ.hasSum
        simpa [hsplit, sub_self] using hconst
      obtain ⟨F, hFF⟩ := Metric.tendsto_atTop.mp htend (ε / 6) hε6
      refine ⟨F, ?_⟩
      have habs : |∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) - 0| < ε / 6 :=
        hFF F le_rfl
      have hnn : 0 ≤ ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) :=
        tsum_nonneg fun y => measureReal_nonneg
      simpa [sub_zero, abs_of_nonneg hnn] using habs
    have hcontF : ContinuousAt
      (fun κ => ∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) * p κ y) θ :=
      tendsto_finsetSum F fun y _ => (hcontm y).mul (hcontp y)
    have hcontFm : ContinuousAt (fun κ => ∑ y ∈ F, (M κ).real (s t ⁻¹' {y})) θ :=
      tendsto_finsetSum F fun y _ => hcontm y
    have hnearF : ∀ᶠ κ in 𝓝 θ,
        |∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) * p κ y -
          ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) * p θ y| < ε / 3 :=
      Metric.tendsto_nhds.mp hcontF (ε / 3) (by positivity)
    have hnearm : ∀ᶠ κ in 𝓝 θ,
        |∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) - ∑ y ∈ F, (M θ).real (s t ⁻¹' {y})| < ε / 6 :=
      Metric.tendsto_nhds.mp hcontFm (ε / 6) hε6
    filter_upwards [hnearF, hnearm] with κ hκF hκm
    have hsumκ := (tsum_state_mass_eq_one (M := M) h_all κ t).2
    have hsplit : ∀ κ' (hsm : Summable fun y => (M κ').real (s t ⁻¹' {y})),
        ∑' y, (M κ').real (s t ⁻¹' {y}) * p κ' y =
          ∑ y ∈ F, (M κ').real (s t ⁻¹' {y}) * p κ' y +
            ∑' y : { y // y ∉ F }, (M κ').real (s t ⁻¹' {y.1}) * p κ' y.1 := by
      intro κ' hsm
      have hsmg : Summable fun y => (M κ').real (s t ⁻¹' {y}) * p κ' y :=
        Summable.of_nonneg_of_le
          (fun y => mul_nonneg measureReal_nonneg (hpIcc κ' y).1)
          (fun y => mul_le_of_le_one_right measureReal_nonneg (hpIcc κ' y).2)
          hsm
      simpa using (hsmg.sum_add_tsum_subtype_compl F).symm
    have htailθ :
      |∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1| ≤
        ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) := by
      have hnn : 0 ≤ ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1 :=
        tsum_nonneg fun y => mul_nonneg measureReal_nonneg (hpIcc θ y.1).1
      rw [abs_of_nonneg hnn]
      refine Summable.tsum_le_tsum ?_ ?_ (hsumθ.subtype _)
      ·
        intro y
        exact mul_le_of_le_one_right measureReal_nonneg (hpIcc θ y.1).2
      · exact (Summable.of_nonneg_of_le
          (fun y => mul_nonneg measureReal_nonneg (hpIcc θ y.1).1)
          (fun y => mul_le_of_le_one_right measureReal_nonneg (hpIcc θ y.1).2)
          (hsumθ.subtype _))
    have htailθ' :
      |∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1| < ε / 6 :=
      lt_of_le_of_lt htailθ hF
    have htailmκ : ∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) < ε / 3 := by
      have h1κ : ∑' y, (M κ).real (s t ⁻¹' {y}) = 1 :=
        (tsum_state_mass_eq_one (M := M) h_all κ t).1
      have h1θ : ∑' y, (M θ).real (s t ⁻¹' {y}) = 1 :=
        (tsum_state_mass_eq_one (M := M) h_all θ t).1
      have hκeq : ∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) =
          1 - ∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) := by
        linarith [hsumκ.sum_add_tsum_subtype_compl F]
      have hθeq : ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) =
          1 - ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) := by
        linarith [hsumθ.sum_add_tsum_subtype_compl F]
      have : |∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) -
          ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1})| < ε / 6 := by
        rw [hκeq, hθeq]
        convert hκm using 1
        simp [abs_sub_comm]
      have hnn : 0 ≤ ∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) :=
        tsum_nonneg fun _ => measureReal_nonneg
      have := (abs_sub_lt_iff.mp this).1
      linarith [hF]
    have htailκ :
      |∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1| < ε / 3 := by
      have hnn : 0 ≤ ∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1 :=
        tsum_nonneg fun y => mul_nonneg measureReal_nonneg (hpIcc κ y.1).1
      rw [abs_of_nonneg hnn]
      refine lt_of_le_of_lt ?_ htailmκ
      refine Summable.tsum_le_tsum ?_ ?_ (hsumκ.subtype _)
      ·
        intro y
        exact mul_le_of_le_one_right measureReal_nonneg (hpIcc κ y.1).2
      · exact (Summable.of_nonneg_of_le
          (fun y => mul_nonneg measureReal_nonneg (hpIcc κ y.1).1)
          (fun y => mul_le_of_le_one_right measureReal_nonneg (hpIcc κ y.1).2)
          (hsumκ.subtype _))
    have : |∑' y, (M κ).real (s t ⁻¹' {y}) * p κ y -
        ∑' y, (M θ).real (s t ⁻¹' {y}) * p θ y| < ε := by
      rw [hsplit κ hsumκ, hsplit θ hsumθ]
      calc
        _ = |(∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) * p κ y -
              ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) * p θ y) +
            ((∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1) -
              ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1)| := by
          ring_nf
        _ ≤ |∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) * p κ y -
              ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) * p θ y| +
            |∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1 -
              ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1| :=
          abs_add_le _ _
        _ ≤ |∑ y ∈ F, (M κ).real (s t ⁻¹' {y}) * p κ y -
              ∑ y ∈ F, (M θ).real (s t ⁻¹' {y}) * p θ y| +
            |∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1| +
            |∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1| := by
          set B := ∑' y : { y // y ∉ F }, (M κ).real (s t ⁻¹' {y.1}) * p κ y.1
          set C := ∑' y : { y // y ∉ F }, (M θ).real (s t ⁻¹' {y.1}) * p θ y.1
          have h2 : |B - C| ≤ |B| + |C| := by
            simpa [Real.norm_eq_abs] using norm_sub_le B C
          linarith
        _ < ε / 3 + ε / 3 + ε / 6 := by
          linarith [hκF, htailκ, htailθ']
        _ < ε := by linarith
    simpa [Real.dist_eq] using this

/-- At a reachable state, the gradient of the trajectory conditional equals the policy gradient. -/
private lemma grad_condProb_eq_grad_policy
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Countable 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Countable 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
  {x : 𝒮}
-- given
  (h_all : ∀ t, (· t) = (r t, s t, a t))
  (hdiff : ∀ x u, Differentiable ℝ (fun κ => M.policy.prob κ x u))
  (hSP : ∀ κ t, SinglePSpace (M κ) (a t, s t))
  (hpos : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : 𝒜) :
-- imply
  ∇[θ] ((M θ).condProb (a t, s t) (u, x)).toReal =
    ∇[θ] (M.policy.prob θ x u) := by
-- proof
  have hc : ContinuousAt (fun κ => (M κ).real (s t ⁻¹' {x})) θ :=
    continuousAt_state_mass (M := M) h_all hdiff t x θ
  have hfd :
    fderiv ℝ (fun κ => ((M κ).condProb (a t, s t) (u, x)).toReal) θ =
      fderiv ℝ (fun κ => M.policy.prob κ x u) θ := by
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne hpos).mono fun κ hne => ?_)
    apply condProb_eq_ofReal_policy (M := M) h_all (hSP κ t) hne u
  simp only [gradient]
  exact congrArg (InnerProductSpace.toDual ℝ Θ).symm hfd

/-- `M.Q` agrees with the trajectory-coordinate form of the action-value under `h_all`. -/
private lemma Q_eq_expect
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (θ : Θ)
  (γ : ℝ)
  (t : ℕ)
  (x : 𝒮)
  (u : 𝒜) :
-- imply
  M.Q θ γ t x u =
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = x ∧ a[t] = u) := by
-- proof
  have hr : r.toFun = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  have hs : s.toFun = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  have ha : a.toFun = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  unfold DensityModel.Q
  simp only [Expectation.asRV_process, Expectation.asRV, AsPathRV.path_fun, Fun.getSliceFrom_eq_function, hr, hs, ha]

/-- `M.V` agrees with the trajectory-coordinate form of the state-value under `h₀`. -/
private lemma V_eq_expect
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (θ : Θ)
  (γ : ℝ)
  (t : ℕ)
  (x : 𝒮) :
-- imply
  M.V θ γ t x =
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:] | s[t] = x) := by
-- proof
  have hr : r.toFun = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  have hs : s.toFun = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  unfold DensityModel.V
  simp only [Expectation.asRV_process, Expectation.asRV, AsPathRV.path_fun, Fun.getSliceFrom_eq_function, hr, hs]

/--
Importance-sampled policy gradient (Schulman et al., arXiv 1506.02438, Proposition 1).
Sampling the action from a proposal parameter `θ'` instead of `θ` replaces the score
`∇ log π_θ` by `∇π_θ / π_θ'`, provided `π_θ'` vanishes only where `π_θ` does.
The state marginal stays the one induced by `θ`.
The alphabets are counting-measure spaces, so neither finiteness nor decidable equality is assumed.
A θ-independent integrable dominate `g` of `‖∇π‖`, with `sup[x] ∫ g < ∞`, replaces the finite-action
constant bound: a uniform bound on `‖∇π‖` is not integrable against counting measure on an infinite alphabet.
`sup[y, u] ‖∇ log π_θ‖ < ∞` bounds the score.

- [advantage policy gradient](?module=Random.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.GtInftySup.A_Function)
- [continuous-action GAE](?module=Random.GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico)
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮]
  [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [μ : CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ θ' : Θ}
  {γ : ℝ}
  {g : 𝒮 → 𝒜 → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r[t], s[t], a[t]))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ x u, M.policy.prob θ' x u ≠ 0 ∨ M.policy.prob θ x u = 0)
  (hg : ∀ κ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) κ‖ ≤ g x u)
  (hintg : ∀ x, Integrable (g x) μ.measure)
  (hcg : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (hφ : StronglyMeasurable (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun κ => Real.log (M.policy.prob κ z.1 z.2)) θ))
  (hMs : sup[y, u] ‖fderiv ℝ (fun κ => Real.log (M.policy.prob κ y u)) θ‖ < ∞) :
-- imply
  haveI : Countable 𝒮 := countable_of_countableMeasure
  haveI : Countable 𝒜 := countable_of_countableMeasure
  have : ∀ θ t, SinglePSpace (M θ) (a[t], s[t]) := fun _ t =>
    SinglePSpace.of.Measurable.Measurable
      (Measurable.of.All_Eq.snd.snd h₁ t)
      (Measurable.of.All_Eq.snd.fst h₁ t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ ↦
    PSpace_Path.of.All_PSpace (fun t ↦ ⟨(Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        ((M.Q θ γ t s[t] a[t] - M.V θ γ t s[t]) •
          ((∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
            (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ))))) := by
-- proof
  intro hSP hsP haP hrP
  obtain ⟨Cg, hcgbound⟩ := id hcg
  have hcgle : ∀ x, ∫ u, g x u ∂μ.measure ≤ Cg := fun x => hcgbound ⟨x, rfl⟩
  obtain ⟨Ms, hMsb⟩ := id hMs
  have hMsle : ∀ y u, ‖fderiv ℝ (fun κ => Real.log (M.policy.prob κ y u)) θ‖ ≤ Ms :=
    fun y u => hMsb ⟨(y, u), rfl⟩
  let A : Θ → ℕ → 𝒮 → 𝒜 → ℝ := fun θ t x u => M.Q θ γ t x u - M.V θ γ t x
  have h₄ : ∀ θ t x u, A θ t x u = M.Q θ γ t x u - M.V θ γ t x :=
    fun _ _ _ _ => rfl
  let : Countable 𝒮 := countable_of_countableMeasure
  let : Countable 𝒜 := countable_of_countableMeasure
  have hmeas : ∀ κ, Measurable (fun z : 𝒮 × 𝒜 => M.policy.prob κ z.1 z.2) :=
    M.policy.measurable_prob
  have hVm : ∀ k, Measurable (M.V θ γ k) := fun _ => Measurable.of_discrete
  have hGAE :=
    GradExpectDotPow_Id.eq.ExpectDotFunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity.In_Ico
      (M := M) (θ := θ) (γ := γ) (g := g)
      (r := r) (s := s) (a := a) h₀ h₁ hmeas hVm h₂ hg hintg hcg hφ hMs
  rw [hGAE]
  set BG : ℝ := (1 - γ)⁻¹ * |M.env.R|
  have hBG : 0 ≤ BG :=
    mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (le_of_lt h₀.2))) (abs_nonneg _)
  have hVbd : ∀ᵐ ω ∂(M θ), ∀ k, |M.V θ γ k (s[k] ω)| ≤ BG :=
    ae_bound_V (M := M) h₀ h₁ θ
  let e : StrongDual ℝ Θ ≃ₗᵢ[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm
  let L := e.toContinuousLinearEquiv
  have hgradLogB : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ Ms := fun y u => by
    simpa [gradient, e, LinearIsometryEquiv.norm_map] using hMsle y u
  have hg0 : ∀ x u, 0 ≤ g x u := fun x u => (norm_nonneg _).trans (hg θ x u)
  have hs_meas : ∀ t, Measurable s[t] := fun t => Measurable.of.All_Eq.snd.fst h₁ t
  have ha_meas : ∀ t, Measurable a[t] := fun t => Measurable.of.All_Eq.snd.snd h₁ t
  have hr_meas : ∀ t, Measurable r[t] := fun t => Measurable.of.All_Eq.fst h₁ t
  have hGbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG := by
    intro t
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ] with ω hr
    have hsum : Summable fun k => γ ^ k * |M.env.R| :=
      (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|
    have hle : ∀ k, ‖γ ^ k * r (t + k) ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hr (t + k))
        (pow_nonneg h₀.1 k)
    have hsn : Summable fun k => ‖γ ^ k * r (t + k) ω‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsum
    have hG : ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω = ∑' k, γ ^ k * r (t + k) ω := by
      simp [Dot.dot, Function.hPow_apply, id_eq, Fun.getSliceFrom]
    rw [hG]
    calc
      _ ≤ ∑' k, ‖γ ^ k * r (t + k) ω‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' k, γ ^ k * |M.env.R| := Summable.tsum_le_tsum hle hsn hsum
      _ = BG := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h₀.1 h₀.2]
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval (Measurable.of.All_Eq.fst h₁)
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ ({ toFun := integ } : Fun ℕ ℝ)[t:]) := by
    intro t
    unfold Dot.dot Fun.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (t + k)) := measurable_pi_apply (t + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hpair_t : ∀ t, Measurable fun ω => (s[t] ω, a[t] ω) := fun t =>
    (hs_meas t).prodMk (ha_meas t)
  have hpair_eq : ∀ t y u,
      (fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(y, u)} =
        s[t] ⁻¹' {y} ∩ a[t] ⁻¹' {u} := fun t y u => by
    ext ω
    simp [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, Prod.ext_iff]
  have hQB_pos (t : ℕ) (x : 𝒮) (u : 𝒜)
    (hpos : (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}) ≠ 0) :
    ‖M.Q θ γ t x u‖ ≤ BG := by
    have hmap : (M θ).map (fun ω => (s[t] ω, a[t] ω)) {(x, u)} ≠ 0 := by
      rwa [Measure.map_apply (hpair_t t) (measurableSet_singleton (x, u))]
    have hQint :
      M.Q θ γ t x u = ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
        ∂(M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}] := by
      rw [Q_eq_expect (M := M) h₁ θ γ t x u]
      simp only [Expectation.asRV, AsPathRV.path_fun]
      exact Expectation.condEval_eq_integral hpR (hpair_t t) (hfG t) hmap
    rw [hQint]
    have hae : ∀ᵐ ω ∂(M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}],
        ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG :=
      cond_absolutelyContinuous.ae_le (hGbd t)
    have : IsProbabilityMeasure
      (M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}] :=
      cond_isProbabilityMeasure hpos
    simpa using
      norm_integral_le_of_norm_le_const
        (μ := (M θ)[|(fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}]) hae
  have hVB_pos (t : ℕ) (x : 𝒮)
    (hpos : (M θ) (s[t] ⁻¹' {x}) ≠ 0) :
    ‖M.V θ γ t x‖ ≤ BG := by
    have hmap : (M θ).map s[t] {x} ≠ 0 := by
      rwa [Measure.map_apply (hs_meas t) (measurableSet_singleton x)]
    have hVint :
      M.V θ γ t x = ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω
        ∂(M θ)[|s[t] ⁻¹' {x}] := by
      rw [V_eq_expect (M := M) h₁ θ γ t x]
      simp only [Expectation.asRV, AsPathRV.path_fun]
      exact Expectation.condEval_eq_integral hpR (hs_meas t) (hfG t) hmap
    rw [hVint]
    have hae : ∀ᵐ ω ∂(M θ)[|s[t] ⁻¹' {x}],
        ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ ≤ BG :=
      cond_absolutelyContinuous.ae_le (hGbd t)
    have : IsProbabilityMeasure (M θ)[|s[t] ⁻¹' {x}] :=
      cond_isProbabilityMeasure hpos
    simpa using
      norm_integral_le_of_norm_le_const (μ := (M θ)[|s[t] ⁻¹' {x}]) hae
  have hAB_pos (t : ℕ) (x : 𝒮) (u : 𝒜)
    (hpos : (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(x, u)}) ≠ 0) :
    ‖A θ t x u‖ ≤ 2 * BG := by
    have hx : (M θ) (s[t] ⁻¹' {x}) ≠ 0 := by
      intro hz
      exact hpos (measure_mono_null (hpair_eq t x u ▸ Set.inter_subset_left) hz)
    calc
      _ = ‖M.Q θ γ t x u - M.V θ γ t x‖ := by rw [h₄]
      _ ≤ ‖M.Q θ γ t x u‖ + ‖M.V θ γ t x‖ := norm_sub_le _ _
      _ ≤ BG + BG := add_le_add (hQB_pos t x u hpos) (hVB_pos t x hx)
      _ = 2 * BG := by ring
  have hposSA : ∀ t, ∀ᵐ ω ∂(M θ),
      (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(s[t] ω, a[t] ω)}) ≠ 0 := by
    intro t
    rw [ae_iff]
    have e :
      {ω : ℕ → ℝ × 𝒮 × 𝒜 |
          ¬(M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(s[t] ω, a[t] ω)}) ≠ 0} =
        ⋃ z ∈ {z : 𝒮 × 𝒜 | (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {z}) = 0},
          (fun ω => (s[t] ω, a[t] ω)) ⁻¹' {z} := by
      ext ω
      simp
    rw [e]
    refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun z hz => hz
  have hQB_ae : ∀ t, ∀ᵐ ω ∂(M θ), ‖M.Q θ γ t (s[t] ω) (a[t] ω)‖ ≤ BG := by
    intro t
    filter_upwards [hposSA t] with ω hpos
    exact hQB_pos t (s[t] ω) (a[t] ω) hpos
  have hVB_ae : ∀ t, ∀ᵐ ω ∂(M θ), ‖M.V θ γ t (s[t] ω)‖ ≤ BG := by
    intro t
    have hS := ae_real_preimage_ne_zero (M := M) hs_meas θ
    filter_upwards [hS] with ω hω
    exact hVB_pos t (s[t] ω)
      (ENNReal.toReal_ne_zero.mp (by simpa [measureReal_def] using hω t)).1
  have hAB_ae : ∀ t, ∀ᵐ ω ∂(M θ), ‖A θ t (s[t] ω) (a[t] ω)‖ ≤ 2 * BG := by
    intro t
    filter_upwards [hposSA t] with ω hpos
    exact hAB_pos t (s[t] ω) (a[t] ω) hpos
  let ψ : ℕ → 𝒮 → Θ := fun t x =>
    𝔼[a : M[x] θ'](
      ((A θ t x a[t] •
        ((∇[θ] (ℙ[M θ](a[t] | s[t] = x) : ℝ)) /
          (ℙ[M[x] θ'](a[t] | s[t] = x) : ℝ)))))
  have hRHS :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      𝔼[a : M[s[t]] θ'](
        ((A θ t s[t] a[t] •
          ((∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ)) /
            (ℙ[M[s[t]] θ'](a[t] | s[t]) : ℝ)))))) =
      𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t s[t]) :=
    rfl
  rw [hRHS]
  let ψπ : ℕ → 𝒮 → Θ := fun t x =>
    𝔼[a : M[x] θ'](
      ((A θ t x a[t] •
        ((∇[θ] (M.policy.prob θ x a[t])) /
          (ℙ[M[x] θ'](a[t] | s[t] = x) : ℝ)))))
  have hψ_eq_ψπ : ∀ t x, ((M θ).real (s.toFun t ⁻¹' {x}) ≠ 0) → ψ t x = ψπ t x := by
    intro t x hpos
    have hgrad : ∀ u,
        ∇[θ] ((M θ).condProb (a[t], s[t]) (u, x)).toReal =
          ∇[θ] (M.policy.prob θ x u) :=
      fun u => grad_condProb_eq_grad_policy (M := M) h₁ h₂ hSP hpos u
    refine congrArg (fun f => Expectation.ofRV (M[x] θ') id f) ?_
    funext u
    simp only [hgrad]
  have hgradPiB : ∀ y u, ‖∇[θ] (M.policy.prob θ y u)‖ ≤ g y u := fun y u => by
    simpa [gradient, e, LinearIsometryEquiv.norm_map] using hg θ y u
  have hψπ_integral : ∀ t x,
      ψπ t x =
        ∫ u, M.policy.prob θ x u •
          (A θ t x u • ∇[θ] Real.log (M.policy.prob θ x u))
          ∂(ReferenceMeasure.measure : Measure 𝒜) := by
    intro t x
    have hsm : AEStronglyMeasurable
      (fun u => A θ t x u •
        ((∇[θ] (M.policy.prob θ x u)) /
          ((M[x] θ').prob (id : 𝒜 → 𝒜) u).toReal))
      ((M[x] θ').map (id : 𝒜 → 𝒜)) :=
      StronglyMeasurable.of_discrete.aestronglyMeasurable
    simp only [ψπ]
    rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hsm]
    simp only [id]
    rw [integral_kernel (M := M) θ' x]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    dsimp only
    rw [kernel_pmf (M := M) θ' x u]
    exact is_weight_eq_score (M := M) h₂ h₃ x u (A θ t x u)
  have hψπB : ∀ t, ∀ᵐ ω ∂(M θ), ‖ψπ t (s[t] ω)‖ ≤ 2 * BG * max Cg 0 := by
    intro t
    have hS := ae_real_preimage_ne_zero (M := M) hs_meas θ
    filter_upwards [hS] with ω hSω
    set x := s[t] ω
    have hxpos : (M θ).real (s[t] ⁻¹' {x}) ≠ 0 := hSω t
    have hterm : ∀ u,
        ‖M.policy.prob θ' x u •
          (A θ t x u • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u))‖ ≤
          2 * BG * g x u := by
      intro u
      if hq : M.policy.prob θ' x u = 0 then
        simp [hq, HDiv.hDiv]
        exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBG) (hg0 x u)
      else
        have hcancel :
          M.policy.prob θ' x u •
            (A θ t x u • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u)) =
            A θ t x u • ∇[θ] (M.policy.prob θ x u) := by
          simp only [HDiv.hDiv]
          rw [smul_smul, smul_smul]
          refine congrArg (fun t => t • ∇[θ] (M.policy.prob θ x u)) ?_
          rw [mul_assoc, mul_comm (A θ t x u), ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
        rw [hcancel, norm_smul, Real.norm_eq_abs]
        if hπ0 : M.policy.prob θ x u = 0 then
          have hgrad0 : ∇[θ] (M.policy.prob θ x u) = 0 := by
            have : fderiv ℝ (fun κ => M.policy.prob κ x u) θ = 0 :=
              IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun κ =>
                show M.policy.prob θ x u ≤ M.policy.prob κ x u from
                  hπ0 ▸ M.policy.nonneg κ x u)
            simpa [gradient] using this
          simp [hgrad0]
          exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBG) (hg0 x u)
        else
          have hmass :=
            joint_ne_zero_of_state_ne_zero (M := M) h₁ (hSP θ t) hxpos hπ0
          exact mul_le_mul (hAB_pos t x u (by rwa [hpair_eq t x u]))
            (hgradPiB x u) (norm_nonneg _) (mul_nonneg (by norm_num) hBG)
    have hinterm : Integrable
      (fun u => M.policy.prob θ' x u •
        (A θ t x u • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u)))
      (ReferenceMeasure.measure : Measure 𝒜) :=
      ((hintg x).smul (2 * BG)).mono' StronglyMeasurable.of_discrete.aestronglyMeasurable
        (Filter.Eventually.of_forall hterm)
    have hψπw : ψπ t x =
        ∫ u, M.policy.prob θ' x u •
          (A θ t x u • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u))
          ∂(ReferenceMeasure.measure : Measure 𝒜) := by
      have hsm : AEStronglyMeasurable
        (fun u => A θ t x u •
          ((∇[θ] (M.policy.prob θ x u)) /
            ((M[x] θ').prob (id : 𝒜 → 𝒜) u).toReal))
        ((M[x] θ').map (id : 𝒜 → 𝒜)) :=
        StronglyMeasurable.of_discrete.aestronglyMeasurable
      simp only [ψπ]
      rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hsm]
      simp only [id]
      rw [integral_kernel (M := M) θ' x]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      dsimp only
      rw [kernel_pmf (M := M) θ' x u]
    rw [hψπw]
    have hle : ‖∫ u, M.policy.prob θ' x u •
        (A θ t x u • ((∇[θ] (M.policy.prob θ x u)) / M.policy.prob θ' x u))
        ∂(ReferenceMeasure.measure : Measure 𝒜)‖ ≤
        ∫ u, 2 * BG * g x u ∂(ReferenceMeasure.measure : Measure 𝒜) :=
      norm_integral_le_of_norm_le ((hintg x).smul (2 * BG))
        (Filter.Eventually.of_forall hterm)
    have hmul : ∫ u, 2 * BG * g x u ∂(ReferenceMeasure.measure : Measure 𝒜) =
        2 * BG * ∫ u, g x u ∂(ReferenceMeasure.measure : Measure 𝒜) := by
      simpa [smul_eq_mul] using integral_smul (2 * BG) (g x)
    have hcg' : ∫ u, g x u ∂(ReferenceMeasure.measure : Measure 𝒜) ≤ max Cg 0 :=
      (hcgle x).trans (le_max_left _ _)
    calc
      _ ≤ 2 * BG * ∫ u, g x u ∂(ReferenceMeasure.measure : Measure 𝒜) := by
        rwa [hmul] at hle
      _ ≤ 2 * BG * max Cg 0 :=
        mul_le_mul_of_nonneg_left hcg' (mul_nonneg (by norm_num) hBG)
  have hgradSm : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => ∇[θ] Real.log (M.policy.prob θ z.1 z.2)) := by
    simp only [gradient]
    exact e.continuous.comp_stronglyMeasurable hφ
  have hdot_state : ∀ (φ : ℕ → 𝒮 → Θ),
      AEStronglyMeasurable
        (fun integ : ℕ → 𝒮 => (γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ φ t (integ t))
        ((M θ).map (AsPathRV.path s)) := by
    intro φ
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t => ?_).aestronglyMeasurable
    exact (StronglyMeasurable.comp_measurable
      (f := fun x : 𝒮 => γ ^ t • φ t x)
      StronglyMeasurable.of_discrete (measurable_pi_apply t))
  have hRHS_int :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t s[t]) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t (s[t] ω)) ∂(M θ) := by
    have : PSpace (M θ) (AsPathRV.path s) := hsP
    refine (OfRV.eq.Integral.of.AEStronglyMeasurable_Map (hdot_state ψ)).trans ?_
    simp only [AsPathRV.path_fun]
  have hψπ_int :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπ t s[t]) =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπ t (s[t] ω)) ∂(M θ) := by
    have : PSpace (M θ) (AsPathRV.path s) := hsP
    refine (OfRV.eq.Integral.of.AEStronglyMeasurable_Map (hdot_state ψπ)).trans ?_
    simp only [AsPathRV.path_fun]
  have hψ_ae : ∀ᵐ ω ∂(M θ), ∀ t, ψ t (s[t] ω) = ψπ t (s[t] ω) := by
    filter_upwards [ae_real_preimage_ne_zero (M := M) hs_meas θ] with ω hω
    intro t
    exact hψ_eq_ψπ t (s[t] ω) (hω t)
  have hψ_ofRV :
    𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψ t s[t]) =
      𝔼[s : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπ t s[t]) := by
    rw [hRHS_int, hψπ_int]
    refine integral_congr_ae ?_
    filter_upwards [hψ_ae] with ω hω
    simp only [Dot.dot, Function.hPow_apply, id_eq, hω]
  rw [hψ_ofRV, hψπ_int]
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
          ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t))))
    ((M θ).map (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a)) :=
    (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      ((htd_meas t).stronglyMeasurable.smul
        (hgradSm.comp_measurable (hpair_path t))).const_smul (γ ^ t)).aestronglyMeasurable
  have hfun :
    (fun integ : (ℕ → ℝ) × (ℕ → 𝒮) × (ℕ → 𝒜) =>
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t =>
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ
          (({ toFun := integ.1 } : Fun ℕ ℝ)[t:] +
            γ • (fun k => M.V θ γ (t + 1 + k) (({ toFun := integ.2.1 } : Fun ℕ 𝒮)[t + 1:] k)) -
            fun k => M.V θ γ (t + k) (({ toFun := integ.2.1 } : Fun ℕ 𝒮)[t:] k))) •
          ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t)))) =
    (fun integ =>
      ∑' t, γ ^ t •
        ((∑' k, γ ^ k * (integ.1 (t + k) + γ * M.V θ γ (t + k + 1) (integ.2.1 (t + k + 1)) -
            M.V θ γ (t + k) (integ.2.1 (t + k)))) •
          ∇[θ] Real.log (M.policy.prob θ (integ.2.1 t) (integ.2.2 t)))) := by
    funext integ
    simp [Dot.dot, Function.hPow_apply, id_eq, Fun.getSliceFrom, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    refine tsum_congr fun t => ?_
    congr 1
    congr 1
    refine tsum_congr fun k => ?_
    have hslice : integ.1[t:] k = integ.1 (t + k) := by
      rfl
    simp [hslice, add_assoc, add_comm, add_left_comm]
  try simp only [hfun]
  rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hLHS_sm]
  simp only [JointRandomSymbol, Expectation.asRV, AsPathRV.path_fun, Dot.dot,
    Function.hPow_apply, id_eq]
  have htd_ae : ∀ᵐ ω ∂(M θ), ∀ t,
      ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω)) =
        ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s[t] ω) := by
    rw [ae_all_iff]
    intro t
    filter_upwards [ae_td_eq_return (M := M) h₀ h₁ hVbd t] with ω hω
    simpa [Dot.dot, Function.hPow_apply, id_eq, Fun.getSliceFrom] using hω
  have hTDbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))‖ ≤ 2 * BG := by
    intro t
    filter_upwards [htd_ae, hGbd t, hVbd] with ω htd hG hV
    have htdt := htd t
    rw [htdt]
    calc
      _ ≤ ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω‖ + ‖M.V θ γ t (s[t] ω)‖ :=
        norm_sub_le _ _
      _ ≤ BG + BG := add_le_add hG (by simpa [Real.norm_eq_abs] using hV t)
      _ = 2 * BG := by ring
  set Cψ : ℝ := 2 * BG * max Cg 0
  set Cl : ℝ := 2 * BG * max Ms 0
  have hCl0 : 0 ≤ Cl :=
    mul_nonneg (mul_nonneg (by norm_num) hBG) (le_max_right _ _)
  have hCψ0 : 0 ≤ Cψ :=
    mul_nonneg (mul_nonneg (by norm_num) hBG) (le_max_right _ _)
  have hMs0 : ∀ y u, ‖∇[θ] Real.log (M.policy.prob θ y u)‖ ≤ max Ms 0 :=
    fun y u => (hgradLogB y u).trans (le_max_left _ _)
  have hψπ_Fint : ∀ t, Integrable (fun ω => γ ^ t • ψπ t (s[t] ω)) (M θ) := by
    intro t
    refine Integrable.of_bound ?_ (γ ^ t * Cψ) ?_
    · exact (StronglyMeasurable.comp_measurable
        (f := fun x : 𝒮 => γ ^ t • ψπ t x)
        StronglyMeasurable.of_discrete (hs_meas t)).aestronglyMeasurable
    ·
      filter_upwards [hψπB t] with ω hB
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
      exact mul_le_mul_of_nonneg_left hB (pow_nonneg h₀.1 t)
  have hψπ_sum : Summable fun t => ∫ ω, ‖γ ^ t • ψπ t (s[t] ω)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun t => ?_) ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right Cψ)
    have hle : ∀ᵐ ω ∂(M θ), ‖γ ^ t • ψπ t (s[t] ω)‖ ≤ γ ^ t * Cψ := by
      filter_upwards [hψπB t] with ω hB
      rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t)]
      exact mul_le_mul_of_nonneg_left hB (pow_nonneg h₀.1 t)
    calc
      _ ≤ ∫ _, γ ^ t * Cψ ∂(M θ) :=
        integral_mono_ae (hψπ_Fint t).norm (integrable_const _) hle
      _ = γ ^ t * Cψ := by
        rw [integral_const]
        simp
  have hRHS_tsum :
    ∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦ ψπ t (s[t] ω)) ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, ψπ t (s[t] ω) ∂(M θ) := by
    simp only [Dot.dot, Function.hPow_apply, id_eq]
    rw [← integral_tsum_of_summable_integral_norm hψπ_Fint hψπ_sum]
    refine tsum_congr fun t => integral_smul (γ ^ t) _
  have hLterm_sm : ∀ t, StronglyMeasurable fun ω =>
      (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
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
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)))) (M θ) := by
    intro t
    refine Integrable.of_bound ((hLterm_sm t).const_smul (γ ^ t)).aestronglyMeasurable
      (γ ^ t * Cl) ?_
    filter_upwards [hTDbd t] with ω htd
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    exact mul_le_mul htd (hMs0 (s[t] ω) (a[t] ω)) (norm_nonneg _)
      (mul_nonneg (by norm_num) hBG)
  have hLbd : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t •
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)))‖ ≤
        γ ^ t * Cl := by
    intro t
    filter_upwards [hTDbd t] with ω htd
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg h₀.1 t), norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 t)
    exact mul_le_mul htd (hMs0 (s[t] ω) (a[t] ω)) (norm_nonneg _)
      (mul_nonneg (by norm_num) hBG)
  have hLsum : Summable fun t => ∫ ω, ‖γ ^ t •
      ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω))) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)))‖ ∂(M θ) := by
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
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω,
        ((∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
            M.V θ γ (t + k) (s (t + k) ω))) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
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
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
        (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s[t] ω)) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    filter_upwards [htd_ae] with ω hω
    rw [hω t]
  rw [integral_congr_ae htdG]
  have hGm : Measurable fun ω => ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω :=
    (hfG t).comp hpR
  have hGscore_bd : ∀ᵐ ω ∂(M θ),
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hGbd t] with ω hG
    rw [norm_smul]
    exact mul_le_mul hG (hMs0 (s[t] ω) (a[t] ω)) (norm_nonneg _) hBG
  have hGscore : Integrable (fun ω =>
      ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    Integrable.of_bound
      (hGm.stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hGscore_bd
  set hVclip : 𝒮 → ℝ := fun y => clip (M.V θ γ t y) (-BG) BG
  have hVclipm : Measurable hVclip := by
    convert hclipm.comp (hVm t)
    rfl
  have hV_eq_clip : ∀ᵐ ω ∂(M θ),
      M.V θ γ t (s[t] ω) = hVclip (s[t] ω) := by
    filter_upwards [hVbd] with ω hv
    have hlo : -BG ≤ M.V θ γ t (s[t] ω) := (abs_le.1 (hv t)).1
    have hhi : M.V θ γ t (s[t] ω) ≤ BG := (abs_le.1 (hv t)).2
    simp only [hVclip]
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have hV0score_bd : ∀ᵐ ω ∂(M θ),
      ‖M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hVbd] with ω hv
    rw [norm_smul]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hv t)
      (hMs0 (s[t] ω) (a[t] ω)) (norm_nonneg _) hBG
  have hV0score : Integrable (fun ω =>
      M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    Integrable.of_bound
      (((hVm t).comp (hs_meas t)).stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hV0score_bd
  have hsplit :
    ∫ ω, ((((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω - M.V θ γ t (s[t] ω)) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
      ∫ ω, (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) -
      ∫ ω, (M.V θ γ t (s[t] ω) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    simp only [sub_smul]
    exact integral_sub hGscore hV0score
  rw [hsplit]
  have hdrop (h : 𝒮 → ℝ) (hh : Measurable h) (hC : ∀ y, ‖h y‖ ≤ BG) :
    ∫ ω, (h (s[t] ω) • ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) = 0 := by
    simp only [gradient]
    have hfun :
      (fun ω => h (s[t] ω) •
        e (fderiv ℝ (fun κ => Real.log (M.policy.prob κ (s[t] ω) (a[t] ω))) θ)) =
      fun ω => L (h (s[t] ω) •
        fderiv ℝ (fun κ => Real.log (M.policy.prob κ (s[t] ω) (a[t] ω))) θ) := by
      funext ω
      exact (L.map_smul (h (s[t] ω)) _).symm
    rw [hfun]
    have hinter : Integrable (fun ω =>
        h (s[t] ω) •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ (s[t] ω) (a[t] ω))) θ) (M θ) :=
      Integrable.of_bound
        ((hh.comp (hs_meas t)).stronglyMeasurable.smul
          (hφ.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
        (BG * max Ms 0) (Filter.Eventually.of_forall fun ω => by
          rw [norm_smul]
          exact mul_le_mul (hC (s[t] ω)) (le_trans (hMsle (s[t] ω) (a[t] ω)) (le_max_left _ _))
            (norm_nonneg _) hBG)
    rw [L.integral_comp_comm (fun ω =>
        h (s[t] ω) •
          fderiv ℝ (fun κ => Real.log (M.policy.prob κ (s[t] ω) (a[t] ω))) θ),
      Integral_SMul.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_Eq_Joint.All_EqWithDensity
        (M := M) θ h₁ h₂ hg hintg h hh hC hφ hMsle t,
      L.map_zero]
  have hV0z :
    ∫ ω, (M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) = 0 := by
    have hclipz := hdrop hVclip hVclipm (by simpa [hVclip] using fun y => hclip_le (M.V θ γ t y))
    have hae : ∀ᵐ ω ∂(M θ),
        M.V θ γ t (s[t] ω) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
          hVclip (s[t] ω) •
            ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
      filter_upwards [hV_eq_clip] with ω h
      rw [h]
    rw [integral_congr_ae hae, hclipz]
  rw [hV0z, sub_zero]
  have hQret :
    ∫ ω, (((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[t:]) ω •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) =
      ∫ ω, (M.Q θ γ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) := by
    have hret := integral_return_smul_eq_cond (M := M) (ψ := fun x u =>
        ∇[θ] Real.log (M.policy.prob θ x u)) h₀ h₁ ⟨max Ms 0, fun x u => hMs0 x u⟩ θ t
    refine hret.trans (integral_congr_ae (ae_of_all _ fun ω => ?_))
    have hq := Q_eq_expect (M := M) h₁ θ γ t (s[t] ω) (a[t] ω)
    simp [hq, Expectation.asRV, AsPathRV.path_fun]
  rw [hQret]
  set hVfreeclip : 𝒮 → ℝ := fun y => clip (M.V θ γ t y) (-BG) BG
  have hVfreeclipm : Measurable hVfreeclip := by
    convert hclipm.comp (Measurable.of_discrete : Measurable (M.V θ γ t))
    rfl
  have hVfree_eq_clip : ∀ᵐ ω ∂(M θ),
      M.V θ γ t (s[t] ω) = hVfreeclip (s[t] ω) := by
    filter_upwards [hVB_ae t] with ω hv
    have hlo : -BG ≤ M.V θ γ t (s[t] ω) := (abs_le.1 (by simpa [Real.norm_eq_abs] using hv)).1
    have hhi : M.V θ γ t (s[t] ω) ≤ BG := (abs_le.1 (by simpa [Real.norm_eq_abs] using hv)).2
    simp only [hVfreeclip]
    rw [clip, max_eq_left hlo, min_eq_left hhi]
  have hVz :
    ∫ ω, (M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) ∂(M θ) = 0 := by
    have hclipz := hdrop hVfreeclip hVfreeclipm
      (by simpa [hVfreeclip] using fun y => hclip_le (M.V θ γ t y))
    have hae : ∀ᵐ ω ∂(M θ),
        M.V θ γ t (s[t] ω) •
          ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) =
          hVfreeclip (s[t] ω) •
            ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
      filter_upwards [hVfree_eq_clip] with ω h
      rw [h]
    rw [integral_congr_ae hae, hclipz]
  have hIntA_bd : ∀ᵐ ω ∂(M θ),
      ‖A θ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ ≤ Cl := by
    filter_upwards [hAB_ae t] with ω hA
    rw [norm_smul]
    exact mul_le_mul hA (hMs0 (s[t] ω) (a[t] ω))
      (norm_nonneg _) (mul_nonneg (by norm_num) hBG)
  have hIntA : Integrable (fun ω =>
      A θ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    Integrable.of_bound
      (StronglyMeasurable.comp_measurable
        (f := fun z : 𝒮 × 𝒜 =>
          A θ t z.1 z.2 • ∇[θ] Real.log (M.policy.prob θ z.1 z.2))
        StronglyMeasurable.of_discrete
        ((hs_meas t).prodMk (ha_meas t))).aestronglyMeasurable
      Cl hIntA_bd
  have hIntV_bd : ∀ᵐ ω ∂(M θ),
      ‖M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))‖ ≤ BG * max Ms 0 := by
    filter_upwards [hVB_ae t] with ω hV
    rw [norm_smul]
    exact mul_le_mul hV (hMs0 (s[t] ω) (a[t] ω))
      (norm_nonneg _) hBG
  have hIntV : Integrable (fun ω =>
      M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) (M θ) :=
    Integrable.of_bound
      (((hVm t).comp (hs_meas t)).stronglyMeasurable.smul
        (hgradSm.comp_measurable ((hs_meas t).prodMk (ha_meas t)))).aestronglyMeasurable
      (BG * max Ms 0) hIntV_bd
  have hfunQV :
    (fun ω => M.Q θ γ t (s[t] ω) (a[t] ω) •
      ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω))) =
    fun ω => A θ t (s[t] ω) (a[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) +
      M.V θ γ t (s[t] ω) •
        ∇[θ] Real.log (M.policy.prob θ (s[t] ω) (a[t] ω)) := by
    funext ω
    have : M.Q θ γ t (s[t] ω) (a[t] ω) =
        A θ t (s[t] ω) (a[t] ω) + M.V θ γ t (s[t] ω) := by
      rw [h₄, sub_add_cancel]
    rw [this, add_smul]
  rw [hfunQV, integral_add hIntA hIntV, hVz, add_zero]
  have hφA : StronglyMeasurable
    (Function.uncurry fun y u =>
      A θ t y u • ∇[θ] Real.log (M.policy.prob θ y u)) :=
    StronglyMeasurable.of_discrete
  let φA : 𝒮 → 𝒜 → Θ := fun y u =>
    A θ t y u • ∇[θ] Real.log (M.policy.prob θ y u)
  let φA₀ : 𝒮 → 𝒜 → Θ := fun y u =>
    if (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(y, u)}) = 0 then 0 else φA y u
  have hφA₀ : StronglyMeasurable (Function.uncurry φA₀) :=
    StronglyMeasurable.of_discrete
  have hCA₀ : ∀ y u, ‖φA₀ y u‖ ≤ Cl := fun y u => by
    simp only [φA₀]
    split_ifs with h0
    ·
      simp
      exact mul_nonneg (mul_nonneg (by norm_num) hBG) (le_max_right _ _)
    ·
      rw [norm_smul]
      exact mul_le_mul (hAB_pos t y u h0) (hMs0 y u) (norm_nonneg _)
        (mul_nonneg (by norm_num) hBG)
  have hφA_ae : (fun ω => φA (s[t] ω) (a[t] ω)) =ᵐ[M θ]
      fun ω => φA₀ (s[t] ω) (a[t] ω) := by
    filter_upwards [hposSA t] with ω hpos
    simp [φA₀, φA, hpos]
  rw [integral_congr_ae hφA_ae,
    Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
      (M := M) h₁ hφA₀ hCA₀ θ t]
  have hinner : ∀ y,
      (∫ u, M.policy.prob θ y u • φA y u
        ∂(ReferenceMeasure.measure : Measure 𝒜)) = ψπ t y :=
    fun y => (hψπ_integral t y).symm
  refine (integral_congr_ae ?_).trans
    (integral_map (μ := M θ) (hs_meas t).aemeasurable
      (f := ψπ t)
      (StronglyMeasurable.of_discrete : StronglyMeasurable (ψπ t)).aestronglyMeasurable)
  have hS := ae_real_preimage_ne_zero (M := M) hs_meas θ
  have hS' : ∀ᵐ y ∂((M θ).map s[t]),
      (M θ).real (s[t] ⁻¹' {y}) ≠ 0 := by
    have hset : MeasurableSet {y : 𝒮 | ¬((M θ).real (s[t] ⁻¹' {y}) ≠ 0)} :=
      MeasurableSet.of_discrete
    rw [ae_iff, Measure.map_apply (hs_meas t) hset]
    have hS_t : ∀ᵐ ω ∂(M θ), (M θ).real (s[t] ⁻¹' {s[t] ω}) ≠ 0 :=
      hS.mono fun ω hω => hω t
    have hpre :
      (fun ω => s[t] ω) ⁻¹' {y : 𝒮 | ¬((M θ).real (s[t] ⁻¹' {y}) ≠ 0)} =
      {ω | ¬((M θ).real (s[t] ⁻¹' {s[t] ω}) ≠ 0)} := by
      ext ω
      simp
    rw [hpre]
    exact ae_iff.mp hS_t
  filter_upwards [hS'] with y hy
  have hpt : ∀ u,
      M.policy.prob θ y u • φA₀ y u =
        M.policy.prob θ y u • φA y u := by
    intro u
    if hπ0 : M.policy.prob θ y u = 0 then
      simp [hπ0]
    else
      have hmass :=
        joint_ne_zero_of_state_ne_zero (M := M) h₁ (hSP θ t) hy hπ0
      have hpos : (M θ) ((fun ω => (s[t] ω, a[t] ω)) ⁻¹' {(y, u)}) ≠ 0 := by
        rwa [hpair_eq t y u]
      simp [φA₀, hpos]
  rw [integral_congr_ae (ae_of_all _ fun u => hpt u), hinner y]


-- created on 2026-11-08
-- updated on 2026-11-14

import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function
import Lemma.Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted
import Lemma.Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.PSpace.of.Measure.eq.Count.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Measure.EqRnDeriv_Count
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology


/--
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t])]`.
`h₁` is the sympy bound `Sup[s[t], t] |γ ** Stack[k](k) @ ∇𝔼[r[t:] | s[t]]| < ∞` (over the reachable
pairs `Pr(s[t] = x) ≠ 0`); `h₂`, `h₃`: `θ ↦ π_θ(u | x)` is differentiable with a bounded gradient
(without them the statement is false, see modelling.md). Densities are taken w.r.t. the counting
measures (`hS`, `hA`), so `ℙ[M.traj θ](a[t] = u | s[t] = x)` is the policy `π_θ(u | x)` at reachable states.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : Sup[t, x | (M.traj θ).real (s t ⁻¹' {x}) ≠ 0]
    ‖∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}]) θ‖ < ∞)
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : Sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M.traj θ) (JointRandomSymbol (a t) (s t)) := fun _ t =>
    Random.PSpace.of.Measure.eq.Count.Measurable ((a_meas t).prodMk (s_meas t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M.traj θ) (s (S := S) (A := A) t) := fun t =>
    ⟨(s_meas t).aemeasurable⟩
  have ha : ∀ t, PSpace (M.traj θ) (a (S := S) (A := A) t) := fun t =>
    ⟨(a_meas t).aemeasurable⟩
  have hr : ∀ t, PSpace (M.traj θ) (r (S := S) (A := A) t) := fun t =>
    ⟨(r_meas t).aemeasurable⟩
  have : PSpace (M.traj θ) (AsPathRV.path (s (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M.traj θ) (AsPathRV.path (a (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M.traj θ) (AsPathRV.path (r (S := S) (A := A))) :=
      PSpace.of_process_path (fun t => ⟨(r_meas t).aemeasurable⟩)
    𝔼[r: M.traj θ](((fun t : ℕ => γ ^ t) @ r))) =
    𝔼[s, a, r : M.traj θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k))) •
          ∇[θ] Real.log (ℙ[M.traj θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t)).toReal)) := by
-- proof
  intro hP _hs _ha _hr _hps _hpa _hpr
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₃o := h₃
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₃
  have hfd : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
    obtain ⟨C, hC⟩ := id h₃
    have hCb : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
    classical
    have hVb : BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => M.V θ γ p.1 p.2) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
      obtain ⟨B, hB⟩ := h₁
      refine ⟨B, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      have h := hB ⟨p, hp, rfl⟩
      simp only [sum_grad_cond M h₂ hCb h₀ p.1 p.2 θ hp] at h
      exact h
    rw [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function
      (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) (fun _ _ _ _ => rfl) (fun θ t x => M.V_eq_integral θ γ t x) hVb h₀ h₂ h₃]
    congr 1
    funext t
    congr 1
    exact (Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted h₀).symm
  obtain ⟨C, hC⟩ := id h₃
  have h₄ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M.traj θ),
      fderiv ℝ (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [reach_ae M θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {s t ω})) θ :=
      (P_diff M h₂ h₄ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [Random.ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  have hold : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ ∂(M.traj θ) := by
    rw [hfd]
    refine tsum_congr fun t => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hscore t] with ω hω
    rw [hω]
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ :=
    { toFun := (InnerProductSpace.toDual ℝ Θ).symm
      invFun := InnerProductSpace.toDual ℝ Θ
      map_add' := map_add _
      map_smul' := fun c φ => by simp
      left_inv := (InnerProductSpace.toDual ℝ Θ).apply_symm_apply
      right_inv := (InnerProductSpace.toDual ℝ Θ).symm_apply_apply
      continuous_toFun := (InnerProductSpace.toDual ℝ Θ).symm.continuous
      continuous_invFun := (InnerProductSpace.toDual ℝ Θ).continuous }
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  -- almost sure bound of the discounted return from `t`
  have hA' : ∀ᵐ ω ∂(M.traj θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [r_bdd_ae M θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  -- the reward series
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M.traj θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M.traj θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M.traj θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (r_bdd_ae M θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M.traj θ') := fun t =>
      Integrable.of_bound ((r_meas t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    · refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M.traj θ') := integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hRb := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded (X := fun _ _ r k => r k)
    h₀ hS hA (fun k => r_meas k) hA' h₂ h₃o
  refine Eq.trans ?_ ((congrArg L hold).trans hRb)
  · rw [← (obj_hasFDerivAt M h₂ h₄ h₀ θ).fderiv, gradient, hL]
    congr 2
    funext θ'
    -- `𝔼[r: M.traj θ']((fun t => γ ^ t) @ r)` is the Bochner integral of the return
    have hr' : ∀ t, PSpace (M.traj θ') (r (S := S) (A := A) t) := fun t =>
      ⟨(r_meas t).aemeasurable⟩
    have hpr' : PSpace (M.traj θ') (AsPathRV.path (r (S := S) (A := A))) :=
      PSpace.of_process_path hr'
    have hpathR :
        Expectation.ofRV (M.traj θ') (Expectation.asRV (r (S := S) (A := A)))
          (fun r => (fun t : ℕ => γ ^ t) @ r) =
          ∫ ω, ∑' t, γ ^ t * r t ω ∂(M.traj θ') := by
      simp only [Expectation.asRV_process, Dot.dot]
      rw [Expectation.ofRV, expectation_real]
      refine (integral_map hpr'.aemeasurable ?_).trans ?_
      · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
          (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
      · rfl
    exact hpathR.trans (hRint θ')


-- created on 2023-04-07
-- updated on 2026-09-29

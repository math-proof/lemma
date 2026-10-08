import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.GtInftySup.Q_Function
import Lemma.Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted
import Lemma.Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Measure.EqRnDeriv_Count
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
import sympy.stats.cond_expectation
import sympy.core.power
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeNormR.le.Abs_R
import Lemma.Random.Measurable_R
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Tensor Measure
open scoped ENNReal.ToRealCoe


/--
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t])]`.
`h₁`, `h₂`: `θ ↦ π_θ(u | x)` is differentiable with a uniformly bounded gradient
(without them the statement is false). The bound on `∇V` over the reachable pairs
`(t, x)` is not assumed: it follows from time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`). Densities are taken w.r.t. the counting
measures (`hS`, `hA`), so `ℙ[M θ](a[t] = u | s[t] = x)` is the policy `π_θ(u | x)` at reachable states.
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
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (action (S := S) (A := A) t, state (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable_A t).prodMk (Random.Measurable_S t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M θ) (state (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_S t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (action (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_A t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (reward (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_R t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (state (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path (action (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path (reward (S := S) (A := A))) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M θ) (AsPathRV.path (reward (S := S) (A := A))) :=
      PSpace.of_process_path (fun t => ⟨(Random.Measurable_R t).aemeasurable⟩)
    𝔼[reward: M θ](((fun t : ℕ => γ ^ t) @ reward))) =
    𝔼[state, action, reward : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => reward (t + k))) •
          ∇[θ] (ℙ[M θ]((PolicyGradient.action t) = action t | (PolicyGradient.state t) = state t) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ _ _
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₂o := h₂
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₂
  have hfd : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, reward t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * reward (t + k) ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (state t ω) (action t ω))) θ ∂(M θ) := by
    obtain ⟨C, hC⟩ := id h₂
    have hCb : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
    classical
    have hr : ∀ t, Measurable (reward (S := S) (A := A) t) := Model.r_meas' (S := S) (A := A)
    have hpR : Measurable (fun ω t ↦ reward (S := S) (A := A) t ω) := measurable_pi_lambda _ hr
    have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
      Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
    have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
        M.Q θ γ t («s.bvar» t) («a.bvar» t) =
          𝔼[reward : M θ]((γ ^ (id : ℕ → ℕ)) @ reward[t:] | state t = «s.bvar» t ∧ action t = «a.bvar» t) := by
      intro θ t sb ab
      symm
      simp only [Expectation.asRV_process]
      rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
      have hpre : JointRandomSymbol (state (S := S) (A := A) t) (action (S := S) (A := A) t) ⁻¹' {(sb t, ab t)} =
          state t ⁻¹' {sb t} ∩ action t ⁻¹' {ab t} := by
        ext ω; simp [JointRandomSymbol, Prod.ext_iff]
      rw [hpre]
      exact Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ θ _ t
    have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
        M.V θ γ t («s.bvar» t) =
          𝔼[reward : M θ]((γ ^ (id : ℕ → ℕ)) @ reward[t:] | state t = «s.bvar» t) := by
      intro θ t sb
      symm
      rw [M.V_eq_integral θ γ t (sb t)]
      simp only [Expectation.asRV_process]
      rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
      rfl
    rw [Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.GtInftySup.Q_Function h₀ hS hA
      (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) hQ_expect hV_expect h₁ h₂o]
    congr 1
    funext t
    congr 1
    exact (Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted h₀).symm
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (state t ω) (action t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (state t ⁻¹' {state t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂o t (state t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  have hold : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, reward t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * reward (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω)) : ℝ).log) θ ∂(M θ) := by
    rw [hfd]
    refine tsum_congr fun t => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hscore t] with ω hω
    rw [hω]
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  -- almost sure bound of the discounted return from `t`
  have hA' : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * reward (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [AeNormR.le.Abs_R (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  -- the reward series
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * reward t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, reward t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * reward t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (AeNormR.le.Abs_R (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * reward t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable_R t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') := integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hRb := Eq.Expect.Sum.Grad.Log.Pr.of.Bounded (X := fun _ _ r k => r k)
    h₀ hS hA (fun k => Random.Measurable_R k) hA' h₁ h₂o
  refine Eq.trans ?_ ((congrArg L hold).trans hRb)
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂o h₀ θ).fderiv, gradient, hL]
  congr 2
  funext θ'
  -- `𝔼[r: M θ']((fun t => γ ^ t) @ r)` is the Bochner integral of the return
  have hr' : ∀ t, PSpace (M θ') (reward (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_R t).aemeasurable⟩
  have hpr' : PSpace (M θ') (AsPathRV.path (reward (S := S) (A := A))) :=
    PSpace.of_process_path hr'
  refine Eq.trans ?_ (hRint θ')
  simp only [Expectation.asRV_process, Dot.dot]
  rw [Expectation.ofRV, expectation_real]
  refine (integral_map hpr'.aemeasurable ?_).trans ?_
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
  · rfl


-- created on 2023-04-07
-- updated on 2026-10-01

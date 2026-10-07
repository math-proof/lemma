import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.GtInftySup.policy_gradient_theorem
import Lemma.Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
import sympy.stats.cond_expectation
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.NormV.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob
import Lemma.Random.Integrable_Fun
import Lemma.Random.Integrable.of.In_Ico
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeNormR.le.Abs_R
import Lemma.Random.Measurable_R
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology
open scoped ENNReal.ToRealCoe


/--
Unbiased advantage estimate: with the advantage
`A[t] = γ ** Stack[k](k) @ (r[t:] + γ * V(s[t+1:]) - V(s[t:]))`,
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • A[t] • ∇ log π(a[t] | s[t])]`
(rewards are bounded by the environment, so both series may be taken inside `𝔼`).
Almost surely `A[t] = γ ** Stack[k](k) @ r[t:] - V(s[t])` (telescoping, using `|V| ≤ (1 - γ)⁻¹ |Rmax|`),
and the baseline term `𝔼[V(s[t]) • ∇ log π(a[t] | s[t])]` vanishes (zero expected score).
The bounds on `V` and `∇V` over the reachable pairs `ℙ(s[t] = x) ≠ 0` are not assumed: `|V|` is bounded
by the reward bound (`Random.NormV.le.MulSub1Abs_R.of.In_Ico`), and `∇V` by time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`).
Densities are taken w.r.t. the counting measures (`hS`, `hA`), so
`ℙ[M θ](s[t] = x)` is the point mass and `ℙ[M θ](a[t] = u | s[t] = x)` is the policy
`π_θ(u | x)` at reachable states; the `SinglePSpace` facts the `ℙ` terms need are derived from `hS`, `hA`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ θ t x, ((M θ) (s t ⁻¹' {x}) ≠ 0) →
    V θ t x = 𝔼[r : M θ](∑' k, γ ^ k * r (t + k) | s t = x))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a (S := S) (A := A) t, s (S := S) (A := A) t) := fun _ t =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable ((a_meas t).prodMk (s_meas t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M θ) (s (S := S) (A := A) t) := fun t =>
    ⟨(s_meas t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a (S := S) (A := A) t) := fun t =>
    ⟨(a_meas t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r (S := S) (A := A) t) := fun t =>
    ⟨(Random.Measurable_R t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (s (S := S) (A := A))) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path (a (S := S) (A := A))) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path (r (S := S) (A := A))) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M θ) (AsPathRV.path (r (S := S) (A := A))) :=
      PSpace.of_process_path (fun t => ⟨(Random.Measurable_R t).aemeasurable⟩)
    𝔼[r: M θ](((fun t : ℕ => γ ^ t) @ r))) =
    𝔼[s, a, r : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k) + γ * V θ (t + k + 1) (s (t + k + 1)) - V θ (t + k) (s (t + k)))) •
          ∇[θ] (ℙ[M θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t) : ℝ).log)) := by
-- proof
  intro hP _hs _ha _hr _hps _hpa _hpr
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  let G : (ℕ → ℝ × S × A) → Θ := fun ω => ∑' t, γ ^ t • ((∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))) • ∇[θ] (ℙ[M θ]((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log)
  have hG : PSpace (M θ) G := ⟨(StronglyMeasurable.tsum fun t => (StronglyMeasurable.smul
      (Measurable.tsum fun k =>
        (((Random.Measurable_R (t + k)).add (((measurable_of_countable (V θ (t + k + 1))).comp (s_meas (t + k + 1))).const_mul γ)).sub
          ((measurable_of_countable (V θ (t + k))).comp (s_meas (t + k)))).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        ∇[θ] (ℙ[M θ]((a t) = p.2 | (s t) = p.1) : ℝ).log)).comp_measurable
          ((s_meas t).prodMk (a_meas t)))).const_smul (γ ^ t)).aestronglyMeasurable.aemeasurable⟩
  have hPs : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    Random.SinglePSpace.of.EqMeasureCount.Measurable (s_meas t) hS
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [Random.AeRealPreimageSS.ne.Zero (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₂ h₃ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [Random.ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  have hVbd : ∀ t x, |M.V θ γ t x| ≤ (1 - γ)⁻¹ * |M.env.R| := fun t x => by
    simpa only [Real.norm_eq_abs] using Random.NormV.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t x
  obtain ⟨B, hBd⟩ : ∃ B : ℝ, ∀ t x, |M.V θ γ t x| ≤ B := ⟨_, hVbd⟩
  have hpR : Measurable (fun ω t ↦ r (S := S) (A := A) t ω) := measurable_pi_lambda _ fun t => Random.Measurable_R t
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ ∑' k, γ ^ k * integ (t + k)) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hVr : ∀ θ' t x, ((M θ').real (s t ⁻¹' {x}) ≠ 0) → (V θ' t x = M.V θ' γ t x) := fun θ' t x hp => by
    have hp' : (M θ') (s t ⁻¹' {x}) ≠ 0 := fun h0 =>
      hp ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 h0)
    rw [h₁ θ' t x hp']
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t), M.V_eq_integral θ' γ t x]
    rfl
  have key : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) -
        V θ (t + k) (s (t + k) ω))) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    have hVae : ∀ᵐ ω ∂(M θ), ∀ k, V θ k (s k ω) = M.V θ γ k (s k ω) :=
      (Random.AeRealPreimageSS.ne.Zero (M := M) θ).mono fun ω h k => hVr θ k _ (h k)
    refine (?_ : _ = ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω))) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)).trans ?_
    swap
    · refine tsum_congr fun t => ?_
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hVae] with ω hω
      simp only [hω]
    congr 1
    funext t
    congr 1
    have h₉ : ∀ᵐ ω ∂(M θ), ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω)) = (∑' k, γ ^ k * r (t + k) ω) - M.V θ γ t (s t ω) := by
      filter_upwards [Random.AeHasSumAndNormG.le.MulSub1Abs_R.of.In_Ico (M := M) θ h₀ t] with ω hG
      have hb : ∀ k, |M.V θ γ k (s k ω)| ≤ B := fun k => hBd k _
      set b : ℕ → ℝ := fun k => γ ^ k * M.V θ γ (t + k) (s (t + k) ω) with hbd
      have hlim : Tendsto b atTop (𝓝 0) :=
        Real.Eq_0.Lim.of.LtAbs.GtInftySup (x := fun k => M.V θ γ (t + k) (s (t + k) ω))
          (by rw [abs_of_nonneg h₀.1]; exact h₀.2) ⟨B, by rintro _ ⟨k, rfl⟩; exact hb (t + k)⟩
      have he : ∀ k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
          M.V θ γ (t + k) (s (t + k) ω)) = γ ^ k * r (t + k) ω + (b (k + 1) - b k) := fun k => by
        simp only [hbd]
        rw [show t + (k + 1) = t + k + 1 by omega]
        ring
      have hbs : Summable (fun k => b (k + 1) - b k) := by
        refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (2 * B))
          fun k => ?_
        calc ‖b (k + 1) - b k‖ ≤ ‖b (k + 1)‖ + ‖b k‖ := norm_sub_le _ _
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
    calc _ = ∫ ω, ((∑' k, γ ^ k * r (t + k) ω) - M.V θ γ t (s t ω)) •
          fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) :=
          integral_congr_ae (h₉.mono fun ω h => by dsimp only; rw [h])
      _ = (∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
            fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) -
          ∫ ω, M.V θ γ t (s t ω) •
            fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
          simp_rw [sub_smul]
          exact integral_sub (Random.Integrable.of.In_Ico (M := M) θ h₀ t
            (fun y u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
            (Random.Integrable_Fun (M := M) θ t (fun y u => M.V θ γ t y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
      _ = _ := by
          have h := Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob (M := M) h₂ θ t (fun y => M.V θ γ t y)
          beta_reduce at h
          rw [h, sub_zero]
  have holdRA : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
      ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) -
        V θ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) := by
    have e1 : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) =
        ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      refine tsum_congr fun t => ?_
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hscore t] with ω hω
      rw [hω]
    have e2 : ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) -
        V θ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
        ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) -
        V θ (t + k) (s (t + k) ω))) •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) := by
      refine tsum_congr fun t => ?_
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hscore t] with ω hω
      rw [hω]
    exact e1.trans (key.trans e2)
  -- almost sure bound of the advantage, uniform in `t`
  have hAdv : ∀ᵐ ω ∂(M θ), ∀ t,
      ‖∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω))‖ ≤
        (1 - γ)⁻¹ * (|M.env.R| + γ * B + B) := by
    filter_upwards [Random.AeNormR.le.Abs_R (M := M) θ, Random.AeRealPreimageSS.ne.Zero (M := M) θ] with ω hr hR t
    have hb : ∀ n, |V θ n (s n ω)| ≤ B := fun n => by
      rw [hVr θ n _ (hR n)]
      exact hBd n _
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₀.1 k)
    calc ‖r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) - V θ (t + k) (s (t + k) ω)‖
        ≤ ‖r (t + k) ω‖ + ‖γ * V θ (t + k + 1) (s (t + k + 1) ω)‖ + ‖V θ (t + k) (s (t + k) ω)‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ |M.env.R| + γ * B + B := by
          rw [norm_mul, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs, Real.norm_eq_abs]
          exact add_le_add (add_le_add (hr _) (mul_le_mul_of_nonneg_left (hb _) h₀.1)) (hb _)
  have hT : ∇[θ] (
      have : PSpace (M θ) (AsPathRV.path (r (S := S) (A := A))) :=
        PSpace.of_process_path (fun t => ⟨(Random.Measurable_R t).aemeasurable⟩)
      𝔼[r: M θ](((fun t : ℕ => γ ^ t) @ r))) =
      𝔼[s, a, r : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k))) •
            ∇[θ] (ℙ[M θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t) : ℝ).log)) :=
    Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.GtInftySup.policy_gradient_theorem h₀ hS hA h₂ h₃
  have hRae : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [Random.AeNormR.le.Abs_R (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  have hRb := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded (X := fun _ _ r k => r k)
    h₀ hS hA (fun k => Random.Measurable_R k) hRae h₂ h₃
  have hAb := Tensor.Eq.Expect.Sum.Grad.Log.Pr.of.Bounded
    (X := fun s _ r k => r k + γ * V θ (k + 1) (s (k + 1)) - V θ k (s k))
    h₀ hS hA
    (fun k => ((Random.Measurable_R k).add (((measurable_of_countable (V θ (k + 1))).comp (s_meas (k + 1))).const_mul γ)).sub
      ((measurable_of_countable (V θ k)).comp (s_meas k)))
    hAdv h₂ h₃
  exact hT.trans (hRb.symm.trans ((congrArg (InnerProductSpace.toDual ℝ Θ).symm holdRA).trans hAb))


-- created on 2023-04-13
-- updated on 2026-10-01

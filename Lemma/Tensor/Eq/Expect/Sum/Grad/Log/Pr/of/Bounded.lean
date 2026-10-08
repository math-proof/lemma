import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.GtInftySup.Q_Function
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
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.Measurable_R
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random


/--
Turning the pointwise integral of the discounted weighted score into the `𝔼[s, a, r : M θ]` sugar.
For a weight `X` (a function of the paths `s`, `a`, `r`) whose discounted tails
`∑' k, γ ^ k * X[t + k]` are almost surely bounded by `B`, the `L`-image (Riesz representative) of
`∑' t, γ ^ t • ∫ (∑' k, γ ^ k * X[t + k]) • d log π(a[t] | s[t])` equals
`𝔼[s, a, r : M θ](∑' t, γ ^ t • ((γ ** Stack[k](k) @ X[t:]) • ∇ log π(a[t] | s[t])))`.
Shared by `policy_gradient_theorem` (`X = r`) and `unbiased_advantage_estimate` (`X = ` advantage).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {X : (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℕ → ℝ}
  {B : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
    X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) k)
  (h₂ : ∀ᵐ ω ∂(M θ), ∀ t,
    ‖∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)‖ ≤ B)
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (action (S := S) (A := A) t, state (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable_A t).prodMk (Random.Measurable_S t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
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
  (InnerProductSpace.toDual ℝ Θ).symm (∑' t, γ ^ t • ∫ ω,
      (∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)) •
        fderiv ℝ (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ ∂(M θ)) =
    𝔼[state, action, reward : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => X state action reward (t + k))) •
          ∇[θ] Real.log (ℙ[M θ]((PolicyGradient.action t) = action t | (PolicyGradient.state t) = state t)).toReal)) := by
-- proof
  intro hP _hs _ha _hr _hps _hpa _hpr
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (state t ω) (action t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (state t ⁻¹' {state t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₃ h₄ t (state t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  let G : (ℕ → ℝ × S × A) → Θ := fun ω => ∑' t, γ ^ t • ((∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)) •
    ∇[θ] Real.log (ℙ[M θ]((action t) = (action t ω) | (state t) = (state t ω))).toReal)
  have hg := fun t : ℕ =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (h₁ (t + k)).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        gradient (fun θ' => Real.log (ℙ[M θ']((action t) = p.2 | (state t) = p.1)).toReal) θ)).comp_measurable
          ((Random.Measurable_S t).prodMk (Random.Measurable_A t)))
  -- bound of the score at the realized pair
  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A, ‖fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' q.1 q.2)) θ‖ :=
    ⟨_, rfl⟩
  have hsc : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖gradient (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ‖ ≤ Ms := by
    intro t
    filter_upwards [hscore t] with ω hω
    rw [gradient, LinearIsometryEquiv.norm_map, hω, hMs]
    have h := Finset.single_le_sum (f := fun q : S × A => ‖fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' q.1 q.2)) θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (state t ω, action t ω))
    exact h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B * Ms := ⟨_, rfl⟩
  have hFb : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t • ((∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ)‖ ≤ γ ^ t * K := by
    intro t
    filter_upwards [h₂, hsc t] with ω h1 h2
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1, hK]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h1 t) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (h1 t))) (pow_nonneg h₀.1 t)
  have hint : ∀ t, Integrable (fun ω =>
      γ ^ t • ((∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ)) (M θ) :=
    fun t => Integrable.of_bound ((hg t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFb t)
  have hsum : Summable fun t => ∫ ω,
      ‖γ ^ t • ((∑' k, γ ^ k * X (fun j => state j ω) (fun j => action j ω) (fun j => reward j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M θ']((action t) = (action t ω) | (state t) = (state t ω))).toReal) θ)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right K)
    calc _ ≤ ∫ _, γ ^ t * K ∂(M θ) := integral_mono_ae (hint t).norm (integrable_const _) (hFb t)
      _ = γ ^ t * K := by simp
  have hGsm : StronglyMeasurable G :=
    StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (hg t).const_smul (γ ^ t)
  -- reconstruct a trajectory from path values (s_path, a_path, r_path)
  let fromPath := fun (p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ)) =>
    fun t => (p.2.2 t, p.1 t, p.2.1 t)
  have fromPath_meas : Measurable fromPath :=
    measurable_pi_lambda _ fun t =>
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)).prodMk
        (((measurable_pi_apply t).comp measurable_fst).prodMk
          ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)))
  -- path-binder form and G define the same Bochner integral
  have hpath :
      𝔼[state, action, reward : M θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => X state action reward (t + k))) •
            ∇[θ] Real.log (ℙ[M θ]((PolicyGradient.action t) = (action t) | (PolicyGradient.state t) = (state t))).toReal)) =
        ∫ ω, G ω ∂(M θ) := by
    have hx : AEMeasurable
        (JointRandomSymbol (AsPathRV.path state)
          (JointRandomSymbol (AsPathRV.path action) (AsPathRV.path reward))) (M θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process, Dot.dot]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    · exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath, G]
          rfl)
    simp only [AsPathRV.path_process, JointRandomSymbol, G]
  rw [hpath, ← integral_tsum_of_summable_integral_norm hint hsum, hL, L.map_tsum]
  refine tsum_congr fun t => ?_
  rw [map_smul, ← L.integral_comp_comm, ← integral_smul]
  congr 1
  funext ω
  rw [map_smul, gradient, hL]


-- created on 2026-09-30
-- updated on 2026-09-30

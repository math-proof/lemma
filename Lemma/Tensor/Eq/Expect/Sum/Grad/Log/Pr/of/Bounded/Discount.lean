import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function
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
`Bounded` with a separate discount `c` for the tails: for a weight `X` whose tails
`∑' k, c ^ k * X[t + k]` are almost surely bounded by `B`, the `L`-image of
`∑' t, γ ^ t • ∫ (∑' k, c ^ k * X[t + k]) • d log π(a[t] | s[t])` equals
`𝔼[s, a, r : M.traj θ](∑' t, γ ^ t • (((c ** Stack[k](k)) @ X[t:]) • ∇ log π(a[t] | s[t])))`.
`c = γ` is `Bounded`; `c = γ * λ` gives the generalized advantage estimate.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ c : ℝ}
  {X : (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℕ → ℝ}
  {B : ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ k, Measurable fun ω : ℕ → S × A × ℝ =>
    X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k)
  (h₂ : ∀ᵐ ω ∂(M.traj θ), ∀ t,
    ‖∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)‖ ≤ B)
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
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
  (InnerProductSpace.toDual ℝ Θ).symm (∑' t, γ ^ t • ∫ ω,
      (∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        fderiv ℝ (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ ∂(M.traj θ)) =
    𝔼[s, a, r : M.traj θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => c ^ k) @ (fun k : ℕ => X s a r (t + k))) •
          ∇[θ] Real.log (ℙ[M.traj θ]((PolicyGradient.a t) = a t | (PolicyGradient.s t) = s t)).toReal)) := by
-- proof
  intro hP _hs _ha _hr _hps _hpa _hpr
  classical
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₄
  obtain ⟨C, hC⟩ := id h₄
  have h₅ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  have hscore : ∀ t, ∀ᵐ ω ∂(M.traj θ),
      fderiv ℝ (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [reach_ae M θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M.traj θ').real (s t ⁻¹' {s t ω})) θ :=
      (P_diff M h₃ h₅ t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [Random.ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
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
  let G : (ℕ → S × A × ℝ) → Θ := fun ω => ∑' t, γ ^ t • ((∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
    ∇[θ] Real.log (ℙ[M.traj θ]((a t) = (a t ω) | (s t) = (s t ω))).toReal)
  have hg := fun t : ℕ =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (h₁ (t + k)).const_mul (c ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun p : S × A =>
        gradient (fun θ' => Real.log (ℙ[M.traj θ']((a t) = p.2 | (s t) = p.1)).toReal) θ)).comp_measurable
          ((s_meas t).prodMk (a_meas t)))
  -- bound of the score at the realized pair
  obtain ⟨Ms, hMs⟩ : ∃ Ms : ℝ, Ms = ∑ q : S × A, ‖fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' q.1 q.2)) θ‖ :=
    ⟨_, rfl⟩
  have hsc : ∀ t, ∀ᵐ ω ∂(M.traj θ),
      ‖gradient (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ‖ ≤ Ms := by
    intro t
    filter_upwards [hscore t] with ω hω
    rw [gradient, LinearIsometryEquiv.norm_map, hω, hMs]
    have h := Finset.single_le_sum (f := fun q : S × A => ‖fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' q.1 q.2)) θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))
    exact h
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B * Ms := ⟨_, rfl⟩
  have hFb : ∀ t, ∀ᵐ ω ∂(M.traj θ),
      ‖γ ^ t • ((∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ)‖ ≤ γ ^ t * K := by
    intro t
    filter_upwards [h₂, hsc t] with ω h1 h2
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1, hK]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h1 t) h2 (norm_nonneg _)
      ((norm_nonneg _).trans (h1 t))) (pow_nonneg h₀.1 t)
  have hint : ∀ t, Integrable (fun ω =>
      γ ^ t • ((∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ)) (M.traj θ) :=
    fun t => Integrable.of_bound ((hg t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFb t)
  have hsum : Summable fun t => ∫ ω,
      ‖γ ^ t • ((∑' k, c ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (ℙ[M.traj θ']((a t) = (a t ω) | (s t) = (s t ω))).toReal) θ)‖ ∂(M.traj θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right K)
    calc _ ≤ ∫ _, γ ^ t * K ∂(M.traj θ) := integral_mono_ae (hint t).norm (integrable_const _) (hFb t)
      _ = γ ^ t * K := by simp
  have hGsm : StronglyMeasurable G :=
    StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (hg t).const_smul (γ ^ t)
  -- reconstruct a trajectory from path values (s_path, a_path, r_path)
  let fromPath := fun (p : (ℕ → S) × (ℕ → A) × (ℕ → ℝ)) =>
    fun t => (p.1 t, p.2.1 t, p.2.2 t)
  have fromPath_meas : Measurable fromPath :=
    measurable_pi_lambda _ fun t =>
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        ((((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))))
  -- path-binder form and G define the same Bochner integral
  have hpath :
      𝔼[s, a, r : M.traj θ](
        ∑' t, γ ^ t •
          (((fun k : ℕ => c ^ k) @ (fun k : ℕ => X s a r (t + k))) •
            ∇[θ] Real.log (ℙ[M.traj θ]((PolicyGradient.a t) = (a t) | (PolicyGradient.s t) = (s t))).toReal)) =
        ∫ ω, G ω ∂(M.traj θ) := by
    have hx : AEMeasurable
        (JointRandomSymbol (AsPathRV.path s)
          (JointRandomSymbol (AsPathRV.path a) (AsPathRV.path r))) (M.traj θ) :=
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


-- created on 2026-10-01

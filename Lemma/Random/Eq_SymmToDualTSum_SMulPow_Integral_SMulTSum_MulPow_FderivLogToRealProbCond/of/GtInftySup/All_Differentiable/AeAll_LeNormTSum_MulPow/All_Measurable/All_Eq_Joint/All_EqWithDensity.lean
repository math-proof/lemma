import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.vector.operators
import sympy.stats.policy_trajectory.continuous_action
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure


/--
Turning the pointwise integral of the discounted weighted density-score into the
`𝔼[r, s, a : M θ]` sugar (continuous-action model).
Continuous-action counterpart of
`Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0`
with density score `∇ log π` (no `ProbCond` / counting measure).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {X : (ℕ → S) → (ℕ → A) → (ℕ → ℝ) → ℕ → ℝ}
  {B Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
    X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) k)
  (h₃ : ∀ᵐ ω ∂(M θ), ∀ t,
    ‖∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)‖ ≤ B)
  (hφ : StronglyMeasurable
    (fun z : S × A =>
      gradient (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u,
    ‖gradient (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace hs
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace ha
  have : PSpace (M θ) (AsPathRV.path r) :=
    PSpace_Path.of.All_PSpace hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  (InnerProductSpace.toDual ℝ Θ).symm (∑' t, γ ^ t • ∫ ω,
      (∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) =
    𝔼[r, s, a : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => X s a r (t + k))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) := by
-- proof
  intro _ _ _ _ _ _
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have hs' : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩
  have ha' : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩
  have hr' : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path s) := PSpace_Path.of.All_PSpace hs'
  have : PSpace (M θ) (AsPathRV.path a) := PSpace_Path.of.All_PSpace ha'
  have : PSpace (M θ) (AsPathRV.path r) := PSpace_Path.of.All_PSpace hr'
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  let G : (ℕ → ℝ × S × A) → Θ := fun ω => ∑' t, γ ^ t •
    ((∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
      gradient (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)
  have hg := fun t : ℕ =>
    StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        (h₂ (t + k)).const_mul (γ ^ k)).stronglyMeasurable
      (hφ.comp_measurable
        ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk
          (Random.Measurable.of.All_Eq.snd.snd h₁ t)))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = B * Ms := ⟨_, rfl⟩
  have hFb : ∀ t, ∀ᵐ ω ∂(M θ),
      ‖γ ^ t • ((∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)‖ ≤ γ ^ t * K := by
    intro t
    filter_upwards [h₃] with ω h1
    rw [norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₀.1, hK]
    ·
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (h1 t) (hMs _ _) (norm_nonneg _) ((norm_nonneg _).trans (h1 t)))
        (pow_nonneg h₀.1 t)
  have hint : ∀ t, Integrable (fun ω =>
      γ ^ t • ((∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)) (M θ) :=
    fun t => Integrable.of_bound ((hg t).const_smul (γ ^ t)).aestronglyMeasurable _ (hFb t)
  have hsum : Summable fun t => ∫ ω,
      ‖γ ^ t • ((∑' k, γ ^ k * X (fun j => s j ω) (fun j => a j ω) (fun j => r j ω) (t + k)) •
        gradient (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ)‖ ∂(M θ) := by
    refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right K)
    calc
      _ ≤ ∫ _, γ ^ t * K ∂(M θ) :=
        integral_mono_ae (hint t).norm (integrable_const _) (hFb t)
      _ = γ ^ t * K := by simp
  have hGsm : StronglyMeasurable G :=
    StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (hg t).const_smul (γ ^ t)
  let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
    fun t => (p.1 t, p.2.1 t, p.2.2 t)
  have fromPath_meas : Measurable fromPath :=
    Measurable.of_eval fun t =>
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
  have hpath :
    𝔼[r, s, a : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => X s a r (t + k))) •
          ∇[θ] Real.log (M.policy.prob θ (s t) (a t)))) =
      ∫ ω, G ω ∂(M θ) := by
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    simp only [AsPathRV.path_process, Dot.dot]
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    ·
      exact (hGsm.comp_measurable fromPath_meas).aestronglyMeasurable.congr
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


-- created on 2026-10-20

import Lemma.Random.Integral_SMul.eq.Zero.of.Le.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Filter Measure


/--
The `c`-discounted sum of residuals against a function of `(s[t], a[t])` reduces to its first term:
`𝔼[(∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])] = 𝔼[δ[t] • ψ(s[t], a[t])]` (generalized advantage estimation).
-/
@[path]
private lemma main
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Model Θ S A}
  {γ c : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : c ∈ Set.Ico 0 1)
  (θ : Θ)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  𝔼[r, s, a : M θ]((∑' k, c ^ k * (r (t + k) + γ * M.Vc θ γ (s (t + k + 1)) -
      M.Vc θ γ (s (t + k)))) • ψ (s t) (a t)) =
    𝔼[r, s, a : M θ]((r t + γ * M.Vc θ γ (s (t + 1)) - M.Vc θ γ (s t)) • ψ (s t) (a t)) := by
-- proof
  intro _ _ _
  classical
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
    fun n => (p.1 n, p.2.1 n, p.2.2 n)
  have fromPath_meas : Measurable fromPath :=
    Measurable.of_eval fun n =>
      ((measurable_pi_apply n).comp measurable_fst).prodMk
        (((measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)))
  have hδj : ∀ j, Measurable fun ω : ℕ → ℝ × S × A =>
      r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω) := fun j =>
    ((Measurable.of.All_Eq.fst h₁ j).add
      (((measurable_of_countable (M.Vc θ γ)).comp
          (Measurable.of.All_Eq.snd.fst h₁ (j + 1))).const_mul γ)).sub
      ((measurable_of_countable (M.Vc θ γ)).comp (Measurable.of.All_Eq.snd.fst h₁ j))
  have hψω : StronglyMeasurable fun ω : ℕ → ℝ × S × A => ψ (s t ω) (a t ω) :=
    (StronglyMeasurable.of_discrete (f := fun p : S × A => ψ p.1 p.2)).comp_measurable
      ((Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Measurable.of.All_Eq.snd.snd h₁ t))
  let δL : (ℕ → ℝ × S × A) → ℝ := fun ω =>
    ∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))
  let ψt : (ℕ → ℝ × S × A) → E := fun ω => ψ (s t ω) (a t ω)
  let Gleft : (ℕ → ℝ × S × A) → E := δL • ψt
  have hGleft : StronglyMeasurable Gleft := by
    convert ((Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
      (hδj (t + k)).const_mul (c ^ k)).stronglyMeasurable).smul hψω
  let δR : (ℕ → ℝ × S × A) → ℝ := fun ω =>
    r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)
  let Gright : (ℕ → ℝ × S × A) → E := δR • ψt
  have hGright : StronglyMeasurable Gright := by
    convert (hδj t).stronglyMeasurable.smul hψω
  let F : ℕ → (ℕ → ℝ × S × A) → E := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
      M.Vc θ γ (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  have hFi : ∀ k, Integrable (F k) (M θ) := fun k => by
    have := (Integrable_SMulSubAddRMul_VcVc.of.In_Ico (M := M) h₀ h₁ θ t (t + k) ψ).smul (c ^ k)
    exact this.congr (Filter.Eventually.of_forall fun ω => (hF k ω).symm)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ, Ψ = ∑ p : S × A, ‖ψ p.1 p.2‖ := ⟨_, rfl⟩
  have hFb : ∀ k, ∀ᵐ ω ∂(M θ), ‖F k ω‖ ≤ c ^ k * ((3 / (1 - γ) - 1) * |M.env.R| * Ψ) := fun k => by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico (M := M) h₀ h₁ θ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₂.1, hΨ]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₂.1 k)
    exact mul_le_mul (h _) (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
      ((norm_nonneg _).trans (h 0))
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right ((3 / (1 - γ) - 1) * |M.env.R| * Ψ))
    calc
      _ ≤ ∫ _, c ^ k * ((3 / (1 - γ) - 1) * |M.env.R| * Ψ) ∂(M θ) :=
        integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * ((3 / (1 - γ) - 1) * |M.env.R| * Ψ) := by
        simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, k ≠ 0 → ∫ ω, F k ω ∂(M θ) = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := Integral_SMul.eq.Zero.of.Le.In_Ico (M := M) t (t + k') h₀ h₁ (Nat.le_add_right t k') θ ψ
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.Vc θ γ (s (t + k'.succ + 1) ω) -
        M.Vc θ γ (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.Vc θ γ (s (t + k' + 1 + 1) ω) - M.Vc θ γ (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M θ) = ∫ ω, F 0 ω ∂(M θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [AeNormSub.le.DeltaBound.of.In_Ico (M := M) h₀ h₁ θ] with ω h
    refine (Summable.tsum_smul_const ?_ _).symm
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₂.1 h₂.2).mul_right
      ((3 / (1 - γ) - 1) * |M.env.R|)) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₂.1]
    exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg h₂.1 k)
  have hint : ∫ ω, Gleft ω ∂(M θ) = ∫ ω, Gright ω ∂(M θ) := by
    change ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) • ψ (s t ω) (a t ω)
      ∂(M θ)
    rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
    simp [F]
  have hL :
    𝔼[r, s, a : M θ]((∑' k, c ^ k * (r (t + k) + γ * M.Vc θ γ (s (t + k + 1)) -
        M.Vc θ γ (s (t + k)))) • ψ (s t) (a t)) =
      ∫ ω, Gleft ω ∂(M θ) := by
    have hx : AEMeasurable
      (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
      PSpace.aemeasurable
    rw [Expectation.ofRV, expectation_bochner]
    refine (integral_map hx ?_).trans ?_
    ·
      exact (hGleft.comp_measurable fromPath_meas).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun p => by
          simp only [Function.comp_apply, fromPath, Gleft, δL, ψt]
          rfl)
    ·
      simp only [AsPathRV.path_process, JointRandomSymbol, Gleft, δL, ψt]
      rfl
  refine hL.trans (hint.trans ?_)
  symm
  have hx : AEMeasurable
    (AsPathRV.path r, AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  rw [Expectation.ofRV, expectation_bochner]
  refine (integral_map hx ?_).trans ?_
  ·
    exact (hGright.comp_measurable fromPath_meas).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun p => by
        simp only [Function.comp_apply, fromPath, Gright, δR, ψt]
        rfl)
  ·
    simp only [AsPathRV.path_process, JointRandomSymbol, Gright, δR, ψt]
    rfl


-- created on 2026-10-06
-- updated on 2026-10-20

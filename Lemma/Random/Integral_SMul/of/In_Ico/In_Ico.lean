import sympy.stats.policy_trajectory.advantage
import sympy.Basic
import Lemma.Random.AeNormSub.le.DeltaBound.of.In_Ico
import Lemma.Random.Integrable_SMulSubAddRMul_VcVc.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Zero.of.Le.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
The `c`-discounted sum of residuals against a function of `(s[t], a[t])` reduces to its first term:
`𝔼[(∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])] = 𝔼[δ[t] • ψ(s[t], a[t])]` (generalized advantage estimation).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ c : ℝ}
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : c ∈ Set.Ico 0 1)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
    M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) • ψ (s t ω) (a t ω)
    ∂(M θ) := by
-- proof
  classical
  let F : ℕ → (ℕ → ℝ × S × A) → E := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
      M.Vc θ γ (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  have hFi : ∀ k, Integrable (F k) (M θ) := fun k => by
    have := (Random.Integrable_SMulSubAddRMul_VcVc.of.In_Ico (M := M) θ h₀ t (t + k) ψ).smul (c ^ k)
    exact this.congr (Filter.Eventually.of_forall fun ω => (hF k ω).symm)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ, Ψ = ∑ p : S × A, ‖ψ p.1 p.2‖ := ⟨_, rfl⟩
  have hFb : ∀ k, ∀ᵐ ω ∂(M θ), ‖F k ω‖ ≤ c ^ k * (M.deltaBound γ * Ψ) := fun k => by
    filter_upwards [Random.AeNormSub.le.DeltaBound.of.In_Ico (M := M) θ h₀] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg h₁.1, hΨ]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h₁.1 k)
    exact mul_le_mul (h _) (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
      ((norm_nonneg _).trans (h 0))
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right (M.deltaBound γ * Ψ))
    calc _ ≤ ∫ _, c ^ k * (M.deltaBound γ * Ψ) ∂(M θ) :=
          integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * (M.deltaBound γ * Ψ) := by simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, k ≠ 0 → ∫ ω, F k ω ∂(M θ) = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := Random.Integral_SMul.eq.Zero.of.Le.In_Ico (M := M) θ h₀ t (t + k') (Nat.le_add_right t k') ψ
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.Vc θ γ (s (t + k'.succ + 1) ω) -
        M.Vc θ γ (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.Vc θ γ (s (t + k' + 1 + 1) ω) - M.Vc θ γ (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M θ) = ∫ ω, F 0 ω ∂(M θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [Random.AeNormSub.le.DeltaBound.of.In_Ico (M := M) θ h₀] with ω h
    have hs : Summable (fun k => c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₁.1 h₁.2).mul_right
        (M.deltaBound γ)) fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₁.1]
      exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg h₁.1 k)
    exact (hs.tsum_smul_const _).symm
  rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
  simp [F]


-- created on 2026-10-06

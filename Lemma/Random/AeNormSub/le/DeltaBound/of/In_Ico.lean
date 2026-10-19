import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint
import Lemma.Random.NormW.le.Abs_R
import Lemma.Random.Vc.eq.TSum_MulPowIntegral.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma Vc_bdd [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (x : S) :
  ‖M.Vc θ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
  rw [Vc.eq.TSum_MulPowIntegral.of.In_Ico (M := M) θ x]
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  apply mul_le_mul_of_nonneg_left (NormW.le.Abs_R (M := M) θ k x) (pow_nonneg hγ.1 k)

/--
Almost surely every temporal-difference residual `δ[j] = r[j] + γ * Vc(s[j+1]) - Vc(s[j])` is bounded by `(3 / (1 - γ) - 1) * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ) :
-- imply
  ∀ᵐ ω ∂(M θ), ∀ j, ‖r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω)‖ ≤
    (3 / (1 - γ) - 1) * |M.env.R| := by
-- proof
  filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω hr j
  calc
    _ ≤ ‖r j ω‖ + ‖γ * M.Vc θ γ (s (j + 1) ω)‖ + ‖M.Vc θ γ (s j ω)‖ :=
      (norm_sub_le _ _).trans (by gcongr; apply norm_add_le)
    _ ≤ (3 / (1 - γ) - 1) * |M.env.R| := by
      rw [norm_mul, Real.norm_of_nonneg h₀.1]
      apply le_trans
      ·
        apply add_le_add
        ·
          apply add_le_add (hr j)
          apply mul_le_mul_of_nonneg_left
          · apply Vc_bdd M θ h₀
          · apply h₀.1
        · apply Vc_bdd M θ h₀
      ·
        have hpos : 0 < 1 - γ := sub_pos.mpr h₀.2
        refine (le_of_eq (b := (2 * (1 - γ)⁻¹) * |M.env.R|) ?_).trans ?_
        ·
          field_simp [hpos.ne']
          ring
        ·
          gcongr
          field_simp [hpos.ne']
          linarith [h₀.1]


-- created on 2026-10-06
-- updated on 2026-10-10

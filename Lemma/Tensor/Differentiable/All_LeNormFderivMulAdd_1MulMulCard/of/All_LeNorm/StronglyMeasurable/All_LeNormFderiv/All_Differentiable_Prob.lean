import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.T.ge.Zero
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma T_sum [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] (M : Model Θ S A) (x : S) (u : A) :
    ∑ y, M.T x u y = 1 := by
  have := M.env.trans_markov
  unfold Model.T
  rw [sum_measureReal_singleton]
  simp

private lemma W_bnd [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A] (M : Model Θ S A) (θ : Θ) {f : ℝ × S × A → ℝ} (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) (y : S) :
    ‖M.W θ f j y‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall (StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j).2)
  show ‖∫ z, M.Kf θ f j z ∂(M.stageK θ y)‖ ≤ _
  simpa using h

private lemma reward_int_bdd [MeasurableSpace S] [MeasurableSpace A] [Fintype A] (M : Model Θ S A) {f : ℝ × S × A → ℝ} {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) (y : S) (u : A) :
    ‖∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u))‖ ≤ C := by
  have := M.env.reward_markov
  have h := norm_integral_le_of_norm_le_const (μ := M.env.reward (y, u))
    (Filter.Eventually.of_forall fun ρ => hC (ρ, y, u))
  simpa using h

/--
If every `θ ↦ π_θ(u | x)` is differentiable with derivative bounded by `Cp` and `‖f‖ ≤ Cf`, then `θ ↦ W θ f j y`
is differentiable with derivative bounded by `(j + 1) * (|A| * Cp * Cf)`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {Cp : ℝ}
  {f : ℝ × S × A → ℝ}
  {Cf : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp)
  (h₂ : StronglyMeasurable f)
  (h₃ : ∀ z, ‖f z‖ ≤ Cf)
  (j : ℕ)
  (y : S) :
-- imply
  Differentiable ℝ (fun θ => M.W θ f j y) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => M.W θ f j y) θ‖ ≤ (j + 1) * (Fintype.card A * Cp * Cf) := by
-- proof
  induction j generalizing y with
  | zero =>
    have e : (fun θ => M.W θ f 0 y) =
        fun θ => ∑ u, M.pol.prob θ y u * ∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u)) :=
      funext fun θ => W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) h₂ h₃ θ y
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((h₀ y u) θ).mul_const _, fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((h₀ y u) θ).mul_const _]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ y u * ∫ ρ, f (ρ, y, u) ∂(M.env.reward (y, u))) θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _u : A, Cf * Cp := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_mul_const ((h₀ y u) θ), norm_smul]
          exact mul_le_mul (reward_int_bdd M h₃ y u) (h₁ θ y u) (norm_nonneg _)
            ((norm_nonneg _).trans (h₃ (0, y, u)))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; push_cast; ring
  | succ j ih =>
    have e : (fun θ => M.W θ f (j + 1) y) =
        fun θ => ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.W θ f j y' :=
      funext fun θ => WAdd_1.eq.Sum_MulProbSum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) h₂ h₃ θ j y
    have hg : ∀ u, Differentiable ℝ (fun θ => ∑ y', M.T y u y' * M.W θ f j y') :=
      fun u θ => DifferentiableAt.fun_sum fun y' _ => ((ih y').1 θ).const_mul _
    have hg' : ∀ u θ, ‖fderiv ℝ (fun θ => ∑ y', M.T y u y' * M.W θ f j y') θ‖ ≤
        (j + 1) * (Fintype.card A * Cp * Cf) := by
      intro u θ
      rw [fderiv_fun_sum fun y' _ => ((ih y').1 θ).const_mul _]
      calc _ ≤ ∑ y', ‖fderiv ℝ (fun θ => M.T y u y' * M.W θ f j y') θ‖ := norm_sum_le _ _
        _ ≤ ∑ y', M.T y u y' * ((j + 1) * (Fintype.card A * Cp * Cf)) := by
            refine Finset.sum_le_sum fun y' _ => ?_
            rw [fderiv_const_mul ((ih y').1 θ), norm_smul, Real.norm_of_nonneg (T.ge.Zero (M := M) y u y')]
            exact mul_le_mul_of_nonneg_left ((ih y').2 θ) (T.ge.Zero (M := M) y u y')
        _ = _ := by rw [← Finset.sum_mul, T_sum, one_mul]
    have hgb : ∀ u θ, ‖∑ y', M.T y u y' * M.W θ f j y'‖ ≤ Cf := by
      intro u θ
      calc _ ≤ ∑ y', ‖M.T y u y' * M.W θ f j y'‖ := norm_sum_le _ _
        _ ≤ ∑ y', M.T y u y' * Cf := by
            refine Finset.sum_le_sum fun y' _ => ?_
            rw [norm_mul, Real.norm_of_nonneg (T.ge.Zero (M := M) y u y')]
            exact mul_le_mul_of_nonneg_left (W_bnd M θ h₂ h₃ j y') (T.ge.Zero (M := M) y u y')
        _ = Cf := by rw [← Finset.sum_mul, T_sum, one_mul]
    rw [e]
    refine ⟨fun θ => DifferentiableAt.fun_sum fun u _ => ((h₀ y u) θ).fun_mul ((hg u) θ), fun θ => ?_⟩
    rw [fderiv_fun_sum fun u _ => ((h₀ y u) θ).fun_mul ((hg u) θ)]
    calc _ ≤ ∑ u, ‖fderiv ℝ (fun θ => M.pol.prob θ y u * ∑ y', M.T y u y' * M.W θ f j y') θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ u, (M.pol.prob θ y u * ((j + 1) * (Fintype.card A * Cp * Cf)) + Cf * Cp) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [fderiv_fun_mul ((h₀ y u) θ) ((hg u) θ)]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_smul, Real.norm_of_nonneg (M.pol.nonneg θ y u)]
            exact mul_le_mul_of_nonneg_left (hg' u θ) (M.pol.nonneg θ y u)
          · rw [norm_smul]
            exact mul_le_mul (hgb u θ) (h₁ θ y u) (norm_nonneg _) ((norm_nonneg _).trans (h₃ (0, y, u)))
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.pol.sum_eq_one, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          push_cast; ring


-- created on 2026-10-06

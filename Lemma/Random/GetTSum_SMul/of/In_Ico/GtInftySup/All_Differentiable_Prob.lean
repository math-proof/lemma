import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Integral_R.eq.Sum_MulRealWRc
import Lemma.Random.Sum_Real.eq.One
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
import Lemma.Random.NormW.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma Er_bdd [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] {r : ℕ → (ℕ → ℝ × S × A) → ℝ} {s : ℕ → (ℕ → ℝ × S × A) → S} {a : ℕ → (ℕ → ℝ × S × A) → A} (h₁ : ∀ t, (· t) = (r t, s t, a t)) (M : Model Θ S A) (θ : Θ) (t : ℕ) :
    ‖∫ ω, r t ω ∂(M θ)‖ ≤ |M.env.R| := by
  rw [Integral_R.eq.Sum_MulRealWRc h₁]
  calc _ ≤ ∑ x, ‖M.env.init.real {x} * M.W θ M.rc t x‖ := norm_sum_le _ _
    _ ≤ ∑ x, M.env.init.real {x} * |M.env.R| := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul, Real.norm_of_nonneg measureReal_nonneg]
        exact mul_le_mul_of_nonneg_left (NormW.le.Abs_R (M := M) θ t x) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, Sum_Real.eq.One, one_mul]

/--
`∇ ∑' t, γ ^ t * 𝔼[r[t]] = ∑' t, γ ^ t • ∇ 𝔼[r[t]]`
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (θ : Θ) :
-- imply
  HasFDerivAt (fun θ => ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ))
    (∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  refine hasFDerivAt_tsum (x₀ := θ) (Set.Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * Cp * |M.env.R|))
    (fun t θ => ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob (M := M) h₁ h₂ hC t).1 θ).hasFDerivAt.const_mul (γ ^ t))
    (fun t θ => ?_) ?_ θ
  · rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob (M := M) h₁ h₂ hC t).2 θ) (pow_nonneg h₀.1 t)
  · refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      fun t => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (Er_bdd h₁ M θ t) (pow_nonneg h₀.1 t)


-- created on 2026-10-06

import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral_R.eq.Sum_MulRealWRc
import Lemma.Random.Sum_Real.eq.One
import Lemma.Random.Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
For a differentiable policy with derivative bounded by `Cp`, `θ ↦ 𝔼[r[t]]` is differentiable with derivative
bounded by `(t + 1) * (|A| * Cp * |R|)`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {Cp : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp)
  (t : ℕ) :
-- imply
  Differentiable ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ‖ ≤
    (t + 1) * (Fintype.card A * Cp * |M.env.R|) := by
-- proof
  have e : (fun θ => ∫ ω, r t ω ∂(M θ)) = fun θ => ∑ x, M.env.init.real {x} * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) t z ∂(M.stageK θ x) :=
    funext fun θ => Integral_R.eq.Sum_MulRealWRc (M := M) h₀ θ t
  rw [e]
  have hW := fun x => Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb (M := M) h₁ h₂ (StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) t x
  refine ⟨fun θ => DifferentiableAt.fun_sum fun x _ => ((hW x).1 θ).const_mul _, fun θ => ?_⟩
  rw [fderiv_fun_sum fun x _ => ((hW x).1 θ).const_mul _]
  calc
    _ ≤ ∑ x, ‖fderiv ℝ (fun θ => M.env.init.real {x} * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) t z ∂(M.stageK θ x)) θ‖ := norm_sum_le _ _
    _ ≤ ∑ x, M.env.init.real {x} * ((t + 1) * (Fintype.card A * Cp * |M.env.R|)) := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [fderiv_const_mul ((hW x).1 θ), norm_smul, Real.norm_of_nonneg measureReal_nonneg]
      exact mul_le_mul_of_nonneg_left ((hW x).2 θ) measureReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, Sum_Real.eq.One, one_mul]


-- created on 2026-10-06
-- updated on 2026-10-12

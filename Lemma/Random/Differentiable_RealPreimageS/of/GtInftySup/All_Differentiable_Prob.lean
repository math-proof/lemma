import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn
import Lemma.Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Real


/--
For a differentiable policy with bounded gradient, `θ ↦ Pr(s[t] = y)` is differentiable.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (t : ℕ)
  (y : S) :
-- imply
  Differentiable ℝ (fun θ => (M θ).real (state t ⁻¹' {y})) := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have e : (fun θ => (M θ).real (state t ⁻¹' {y})) = fun θ => ∑ x, M.env.init.real {x} * M.Pn θ t x y :=
    funext fun θ => Random.RealPreimageS.eq.Sum_MulRealPn (M := M) θ t y
  rw [e]
  exact fun θ => DifferentiableAt.fun_sum fun x _ =>
    ((Tensor.Differentiable.All_LeNormFderivMulAdd_1MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_Differentiable_Prob (M := M) h₀ hC (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) t x).1 θ).const_mul _


-- created on 2026-10-06

import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Real.Norm_Eq12.le.One
import Lemma.Random.Pn.eq.Integral
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn
import Lemma.Random.Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
For a differentiable policy with bounded gradient, `θ ↦ Pr(s[t] = y)` is differentiable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (t : ℕ)
  (y : S) :
-- imply
  Differentiable ℝ (fun θ => (M θ).real (s t ⁻¹' {y})) := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₂
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have e : (fun θ => (M θ).real (s t ⁻¹' {y})) =
      fun θ => ∑ x, M.env.init.real {x} *
        ∫ z, M.Kf θ (fun z => if z.2.1 = y then (1:ℝ) else 0) t z ∂(M.stageK θ x) :=
    funext fun θ =>
      (RealPreimageS.eq.Sum_MulRealPn (M := M) h₀ θ t y).trans
        (by simp_rw [Pn.eq.Integral (M := M) θ t _ y])
  rw [e]
  exact fun θ => DifferentiableAt.fun_sum fun x _ =>
    ((Differentiable.All_LeNormFderiv_MulAdd_1_MulMulCard.of.All_LeNorm.StronglyMeasurable.All_LeNormFderiv.All_All_Differentiable_FunPolProb (M := M) h₁ hC (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) t x).1 θ).const_mul _


-- created on 2026-10-06

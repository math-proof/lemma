import Def.Analysis.Calculus.Gradient.Operators.Part2
import Syntax.Order.Sup
import Lemma.Set.Summable_MulPowMulAdd_1.of.In_Ico
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
import Lemma.Random.NormW.le.Abs_R
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Set
set_option linter.unusedVariables false


/--
the gradients of the state-value function are bounded over the reachable pairs `(t, x)`:
by definition `V θ γ t x = V0 θ γ x`, and `S` is finite
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (θ : Θ) :
-- imply
  BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => M.V θ γ p.1 p.2) θ‖) ''
    {p | (M θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
-- proof
  refine ⟨∑ x, ‖fderiv ℝ (fun θ => M.V0 θ γ x) θ‖, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  beta_reduce
  simp only [Model.V]
  apply Finset.single_le_sum (f := fun x => ‖fderiv ℝ (fun θ => M.V0 θ γ x) θ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ p.2)


-- created on 2026-10-06
-- updated on 2026-11-03

import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function
import Lemma.Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Policy-gradient theorem (REINFORCE form):
`γ ** Stack[t](t) @ ∇𝔼[r] = ∑' t, γ ^ t • 𝔼[(γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t])]`.
`h₁` is the sympy bound `Sup[s[t], t] |γ ** Stack[k](k) @ ∇𝔼[r[t:] | s[t]]| < ∞` (over the reachable
pairs `Pr(s[t] = x) ≠ 0`); `h₃`, `h₄`: `θ ↦ π_θ(u | x)` is differentiable with a bounded gradient
(without them the statement is false, see modelling.md).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
-- given
  (h₀ : ∀ t, IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : BddAbove ((fun p : ℕ × S =>
    ‖∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (p.1 + k) ω ∂(M.traj θ)[|s p.1 ⁻¹' {p.2}]) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}))
  (h₂ : γ ∈ Set.Ico 0 1)
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖)) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
    ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * r (t + k) ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
-- proof
  obtain ⟨C, hC⟩ := id h₄
  have h₅ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  have h₆ : BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => M.V θ γ p.1 p.2) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
    obtain ⟨B, hB⟩ := h₁
    refine ⟨B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have h := hB ⟨p, hp, rfl⟩
    simp only [sum_grad_cond M h₃ h₅ h₂ p.1 p.2 θ hp] at h
    exact h
  rw [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function
    (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) h₀ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) h₆ h₂ h₃ h₄]
  congr 1
  funext t
  congr 1
  exact (Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted (h₀ t) h₂).symm


-- created on 2026-09-26

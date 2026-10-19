import Lemma.Random.Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Policy-gradient recursion for the model value functions on a reachable state x (h₄ : Pr(s[t] = x) ≠ 0):
∇V(t, x) = ∑ u, Q(t, x, u) • ∇π(u | x) + γ • ∑ y, P1(x, y) • ∇V(t+1, y),
where V and Q are the local state / action values
`𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)` and
`𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)`,
P1 θ x y = Pr(s[t+1] = y | s[t] = x),
and θ ↦ π_θ(u | x) is differentiable (h₂) with a bounded gradient (h₃).
Gradient (Riesz representative) form of `Random.Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {x : S}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  let V (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  ∇[θ] V θ t x =
    ∑ u, Q θ t x u • ∇[θ] M.policy.prob θ x u +
      γ • ∑ y, M.P1 θ x y • ∇[θ] V θ (t + 1) y := by
-- proof
  classical
  simpa [gradient, map_add, map_smul, map_sum] using
    congrArg (InnerProductSpace.toDual ℝ Θ).symm
      (Fderiv.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob t x θ h₀ h₁ h₂ h₃ h₄)


-- created on 2026-10-06
-- updated on 2026-10-10

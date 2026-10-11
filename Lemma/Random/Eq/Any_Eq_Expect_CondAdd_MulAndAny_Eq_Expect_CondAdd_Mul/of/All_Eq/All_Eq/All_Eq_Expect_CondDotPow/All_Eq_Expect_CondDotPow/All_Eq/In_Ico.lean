import Lemma.Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico
import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
py `Random.Eq.Any_Eq_Expect_CondAdd_MulAndAny_Eq_Expect_CondAdd_Mul.of.All_Eq.All_Eq.All_Eq_Expect_CondDotPow.All_Eq_Expect_CondDotPow.All_Eq.In_Ico`:
if \(Q^\pi,V^\pi\) satisfy the Bellman equation and \(Q^\star,V^\star\) are the policy-wise
suprema, then the optimal Bellman identities hold
\(V^\star=\max_a Q^\star\), \(V^\star=\mathbb E[r+\gamma V^\star\mid s]\),
\(Q^\star=\mathbb E[r+\gamma V^\star\mid s,a]\).
Left `sorry` (py `@prove(proved=False)`); the non-optimal case is
`Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [Nonempty A]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ] [Nonempty Θ]
  {M : Model Θ S A}
  {γ : ℝ}
  {t : ℕ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {Qstar : ℕ → S → A → ℝ}
  {Vstar : ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
    Q θ t («s.bvar» t) («a.bvar» t) =
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S),
    V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (hQstar : ∀ t x u, Qstar t x u = ⨆ θ, Q θ t x u)
  (hVstar : ∀ t x, Vstar t x = ⨆ θ, V θ t x)
  («s.bvar» : ℕ → S)
  («a.bvar» : ℕ → A) :
-- imply
  Vstar t («s.bvar» t) = ⨆ u, Qstar t («s.bvar» t) u ∧
    (∃ θ, Vstar t («s.bvar» t) =
      𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) | s t = «s.bvar» t)) ∧
    (∃ θ, Qstar t («s.bvar» t) («a.bvar» t) =
      𝔼[r, s : M θ](r t + γ * Vstar (t + 1) (s (t + 1)) |
        s t = «s.bvar» t ∧ a t = «a.bvar» t)) := by
-- proof
  sorry


-- created on 2026-10-11

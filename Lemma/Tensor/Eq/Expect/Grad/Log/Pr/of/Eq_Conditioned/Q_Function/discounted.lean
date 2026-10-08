import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.Integral_SMul.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`𝔼[∇ log π(a[t] | s[t]) * (γ ** Stack[k](k) @ r[t:])] =
  𝔼[∇ log π(a[t] | s[t]) * (γ ** Stack[k](k) @ 𝔼[r[t:] | s[t], a[t]])]`
(law of iterated expectation on `(s[t], a[t])`).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  ∫ ω, (∑' k, γ ^ k * r (t + k) ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
    ∫ ω, (∑' k, γ ^ k * ∫ ω', r (t + k) ω' ∂(M θ)[|s t ⁻¹' {s t ω} ∩ a t ⁻¹' {a t ω}]) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  classical
  exact Random.Integral_SMul.of.In_Ico (M := M) h₀ h₁ θ t (fun x u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ)


-- created on 2023-04-01

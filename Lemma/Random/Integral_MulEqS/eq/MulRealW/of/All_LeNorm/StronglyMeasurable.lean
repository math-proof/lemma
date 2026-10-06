import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
`𝔼[1{s[t] = x} * f(ω[t + j])] = Pr(s[t] = x) * W θ f j x` for a bounded strongly measurable stage function `f`
(trajectory model `M`, time-homogeneous `j`-step kernel expectation `W`).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (θ : Θ)
  (h₀ : StronglyMeasurable f)
  (h₁ : ∀ z, ‖f z‖ ≤ C)
  (t j : ℕ)
  (x : S) :
-- imply
  ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f (ω (t + j)) ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.W θ f j x := by
-- proof
  have hK := Kf_bdd M θ h₀ h₁ j
  exact (stage_iter M θ h₀ h₁ t j (ind_fst_sm x) (ind_bdd _)).trans (stage_split M θ t hK.1 hK.2 x)


-- created on 2026-10-06

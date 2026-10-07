import sympy.stats.policy_trajectory.gradient

/-!
# Temporal-difference residuals (generalized advantage estimation): definitions

Definitions only (repo rule: `sympy/` holds definitions, theorems live in `Lemma/`):

* `deltaBound M γ`, the bound of the temporal-difference residual
  `δ[j] = r[j] + γ * Vc(s[j+1]) - Vc(s[j])`.

The zero-mean property `𝔼[δ[n+1] • ψ(s[t], a[t])] = 0` (`t ≤ n`,
`Random.Integral_SMul.eq.Zero.of.Le.In_Ico`) and its consequence
`𝔼[(∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])] = 𝔼[δ[t] • ψ(s[t], a[t])]`
(`Random.Integral_SMul.of.In_Ico.In_Ico`, the GAE identity), together with their helpers, live in
`Lemma/Random/*`; see the 2026-10-06 breaking-change entry in `AGENTS.md` for the name map.
-/
open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- the bound of the temporal-difference residual `δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` -/
noncomputable def deltaBound (M : Model Θ S A) (γ : ℝ) : ℝ :=
  |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) + (1 - γ)⁻¹ * |M.env.R|

end Model

end PolicyGradient

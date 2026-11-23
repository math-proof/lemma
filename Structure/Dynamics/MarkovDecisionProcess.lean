module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Class.Probability.Rv
public import Notation.Fun

public section

open MeasureTheory ProbabilityTheory
open Fun

universe u v

/-!
# Markov decision processes

Ported from rl-theory-in-lean `RLTheory/MarkovDecisionProcess/MarkovDecisionProcess.lean`.

* `MDPSpec S A`: initial distribution `p₀`, transition law `P (s, a)`, reward `r` and discount `γ`.
* `MDPSpec.pi_kernel pi`, `MDPSpec.pi_kernel₁ pi`: a stationary policy `pi : S → ProbabilityMeasure A`
  as a Markov kernel `S → A`, resp. `(S × A) × S → A` (reading the last state).
* `MDPSpec.transition_kernel`: `P` as a Markov kernel `S × A → S`.
* `MDPSpec.induced_chain pi`: the Markov chain on state–action pairs induced by `pi`.
* `FiniteMDP S A`: an MDP on finite spaces with a policy whose induced chain is irreducible and
  aperiodic and `γ ∈ [0, 1)`; `FiniteMDP.MRP` is the induced `FiniteMRP (S × A)`.

The policy-gradient structures `StochasticMDP`, `Policy`, and `Model` (namespace `PolicyGradient`)
also live in this module.
-/

-- MDP data (rl: `ReinforcementLearning.MDPSpec`)
structure MDPSpec (S : Type u) (A : Type v) [MeasurableSpace S] [MeasurableSpace A] where
  p₀ : ProbabilityMeasure S
  P : S × A → ProbabilityMeasure S
  r : S × A → ℝ
  γ : ℝ

namespace PolicyGradient

/-- Standard stochastic MDP environment with bounded rewards. -/
structure StochasticMDP (𝒮 𝒜 : Type*) [MeasurableSpace 𝒮] [MeasurableSpace 𝒜] where
  init : ProbabilityMeasure 𝒮
  trans : 𝒮 × 𝒜 → ProbabilityMeasure 𝒮
  reward : 𝒮 × 𝒜 → ProbabilityMeasure ℝ
  reward_bdd : ∃ R, ∀ p, (reward p : Measure ℝ) (Set.Icc (-R) R) = 1

/-- A parameterized policy `π θ sₜ aₜ = π_θ(aₜ | sₜ)` on a general (e.g. continuous) action space. -/
structure Policy (Θ 𝒮 𝒜 : Type*) [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] where
  π : Θ → 𝒮 → 𝒜 → ℝ

/-- A policy-gradient model is a `StochasticMDP` together with a density policy
on a general action space. -/
structure Model (Θ 𝒮 𝒜 : Type*) [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
    extends StochasticMDP 𝒮 𝒜, Policy Θ 𝒮 𝒜

end PolicyGradient

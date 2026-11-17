module

public import Structure.Dynamics.MarkovDecisionProcess
public import Class.Probability.Rv
public import Notation.Fun
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

public section

open MeasureTheory ProbabilityTheory
open Fun

namespace PolicyGradient

/-!
# Stochastic policies

`StochasticPolicy` records that a parameterized `Policy` density `π[θ]` is nonnegative,
integrates to one with respect to the action-space reference measure, and is jointly measurable.
Access the assumptions as `hp.nonneg` when the instance is `[hp : StochasticPolicy p]`
(not `p.nonneg`, and not `StochasticPolicy.nonneg p`).
-/

/-- `π` is a probability density of the action given the state, w.r.t. the reference measure of `𝒜`
(for a finite action space with counting measure, `integral_eq_one` is the usual `sum_eq_one`). -/
class StochasticPolicy {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
    (p : Policy Θ 𝒮 𝒜) : Prop where
  nonneg : ∀ (θ : Θ) sₜ aₜ, 0 ≤ p.π[θ] sₜ aₜ
  integral_eq_one : ∀ (θ : Θ) sₜ, ∫ aₜ, p.π[θ] sₜ aₜ ∂μ.measure = 1
  measurable_π : ∀ (θ : Θ), Measurable (fun (sₜ, aₜ) => p.π[θ] sₜ aₜ)

end PolicyGradient

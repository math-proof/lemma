import Structure.Dynamics.MarkovDecisionProcess
import Class.Probability.Rv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Kernel.WithDensity
import Def.Order.Miscellaneous
import Lemma.Random.SinglePSpace.of.Eq_WithDensity.Measurable.AEMeasurable
import Lemma.Random.SinglePSpace.of.AEMeasurable.Distributed
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Class.Dynamics.PolicyTrajectory
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-!
# Canonical `IsPolicyTrajectory` instance

Registers the canonical stage projections
`fun t ω => (ω t).1`, `fun t ω => (ω t).2.1`, and `fun t ω => (ω t).2.2`
as a `Model.IsPolicyTrajectory`.
-/


namespace PolicyGradient

variable {Θ 𝒮 𝒜 : Type*} [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]

namespace Model.IsPolicyTrajectory

variable {M : Model Θ 𝒮 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}

/-- Canonical projections form an `IsPolicyTrajectory` (`stage_eq` by `rfl`). -/
instance instCanonical (M : Model Θ 𝒮 𝒜) :
    Model.IsPolicyTrajectory M ⟨fun t ω => (ω t).1⟩ ⟨fun t ω => (ω t).2.1⟩ ⟨fun t ω => (ω t).2.2⟩ where
  stage_eq t := by
    funext ω
    rfl

end Model.IsPolicyTrajectory
end PolicyGradient

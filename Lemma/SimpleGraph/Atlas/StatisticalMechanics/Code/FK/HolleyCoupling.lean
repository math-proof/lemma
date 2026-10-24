import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.HolleyCoupling
open MeasureTheory Finset StatMech StatMech.FK


/--
[measOfMass_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma measOfMass_apply_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  measOfMass μ A = ∑ ω : ConfigSpace E, if ω ∈ A then ENNReal.ofReal (μ ω) else 0 := by
-- proof
  apply StatMech.FK.measOfMass_apply μ A

/--
[measOfMass_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma measOfMass_isProbabilityMeasure_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hsum : ∑ ω, μ ω = 1) :
-- imply
  IsProbabilityMeasure (measOfMass μ) := by
-- proof
  apply StatMech.FK.measOfMass_isProbabilityMeasure μ hμ hsum

/--
[measOfMass_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma measOfMass_real_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hμ : 0 ≤ μ) :
-- imply
  (measOfMass μ).real A = ∑ ω : ConfigSpace E, if ω ∈ A then μ ω else 0 := by
-- proof
  apply StatMech.FK.measOfMass_real μ hμ A

/--
[measOfMass_real_eq_indicator_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma measOfMass_real_eq_indicator_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hμ : 0 ≤ μ) :
-- imply
  (measOfMass μ).real A = ∑ ω : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) ω * μ ω := by
-- proof
  apply StatMech.FK.measOfMass_real_eq_indicator_sum μ hμ A

/--
[holley_stochasticallyDominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma holley_stochasticallyDominated_eq
  [Fintype E]
  [DecidableEq E]
  {μ₁ μ₂ : ConfigSpace E → ℝ}
-- given
  (h₁ : 0 ≤ μ₁)
  (h₂ : 0 ≤ μ₂)
  (hsum : ∑ ω, μ₁ ω = ∑ ω, μ₂ ω)
  (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
-- imply
  measOfMass μ₁ ≼ measOfMass μ₂ := by
-- proof
  apply StatMech.FK.holley_stochasticallyDominated h₁ h₂ hsum hcond

/--
[holley_exists_monotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma holley_exists_monotoneCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {μ₁ μ₂ : ConfigSpace E → ℝ}
-- given
  (h₁ : 0 < μ₁)
  (h₂ : 0 < μ₂)
  (hn₁ : ∑ ω, μ₁ ω = 1)
  (hn₂ : ∑ ω, μ₂ ω = 1)
  (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
-- imply
  ∃ κ : Measure (ConfigSpace E × ConfigSpace E), IsFiniteMeasure κ ∧ MonotoneCoupling (measOfMass μ₁) (measOfMass μ₂) κ := by
-- proof
  apply StatMech.FK.holley_exists_monotoneCoupling h₁ h₂ hn₁ hn₂ hcond

/--
[holley_dominates_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HolleyCoupling.lean)
-/
@[path]
private lemma holley_dominates_measure_eq
  [Fintype E]
  [DecidableEq E]
  {μ₁ μ₂ : ConfigSpace E → ℝ}
-- given
  (h₁ : 0 < μ₁)
  (h₂ : 0 < μ₂)
  (hn₁ : ∑ ω, μ₁ ω = 1)
  (hn₂ : ∑ ω, μ₂ ω = 1)
  (hcond : ∀ a b, μ₁ a * μ₂ b ≤ μ₁ (a ⊓ b) * μ₂ (a ⊔ b)) :
-- imply
  measOfMass μ₁ ≼ measOfMass μ₂ := by
-- proof
  apply StatMech.FK.holley_dominates_measure h₁ h₂ hn₁ hn₂ hcond


-- created on 2026-10-23

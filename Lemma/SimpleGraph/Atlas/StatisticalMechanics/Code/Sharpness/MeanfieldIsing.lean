import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsing
open MeasureTheory Real Set StatMech StatMech.Sharpness


/--
[meanfield_ode_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsing.lean)
-/
@[path]
private lemma meanfield_ode_antitone_eq
  {β₀ : ℝ}
  {u : ℝ → ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ u β)
  (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - u β) ≤ deriv u β) :
-- imply
  AntitoneOn (fun β => β ^ 2 * (1 - u β)) (Ici β₀) := by
-- proof
  apply StatMech.Sharpness.meanfield_ode_antitone β₀ hβ₀ u hdiff hineq

/--
[meanfield_one_minus_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsing.lean)
-/
@[path]
private lemma meanfield_one_minus_le_eq
  {β₀ : ℝ}
  {u : ℝ → ℝ}
  {β : ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ u β)
  (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - u β) ≤ deriv u β)
  (hβ : β₀ ≤ β) :
-- imply
  1 - u β ≤ (β₀ / β) ^ 2 * (1 - u β₀) := by
-- proof
  apply StatMech.Sharpness.meanfield_one_minus_le β₀ hβ₀ u hdiff hineq hβ

/--
[meanfield_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsing.lean)
-/
@[path]
private lemma meanfield_lower_bound_eq
  {β₀ : ℝ}
  {m : ℝ → ℝ}
  {β : ℝ}
-- given
  (hβ₀ : 0 < β₀)
  (hdiff : ∀ β ∈ Ici β₀, DifferentiableAt ℝ (fun β => (m β) ^ 2) β)
  (hineq : ∀ β ∈ Ioi β₀, (2 / β) * (1 - (m β) ^ 2) ≤ deriv (fun β => (m β) ^ 2) β)
  (hzero : m β₀ = 0)
  (hnonneg : ∀ β ∈ Ici β₀, 0 ≤ m β)
  (hβ : β₀ ≤ β) :
-- imply
  Real.sqrt (1 - (β₀ / β) ^ 2) ≤ m β := by
-- proof
  apply StatMech.Sharpness.meanfield_lower_bound β₀ hβ₀ m hdiff hineq hzero hnonneg hβ


-- created on 2026-10-23

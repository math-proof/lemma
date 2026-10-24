import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.ThresholdLift
open Set StatMech StatMech.BeffaraDC


/--
[thresholdLift_of_logisticDiffineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ThresholdLift.lean)
-/
@[path]
private lemma thresholdLift_of_logisticDiffineq_eq
  {f f' : ℝ → ℝ}
  {p₁ p₂ κ a : ℝ}
-- given
  (hp : p₁ ≤ p₂)
  (hκ : 0 ≤ κ)
  (ha : 0 < a)
  (hf01 : ∀ p ∈ Icc p₁ p₂, f p ∈ Icc (0 : ℝ) 1)
  (hderiv : ∀ p ∈ Icc p₁ p₂, HasDerivAt f (f' p) p)
  (hdiff : ∀ p ∈ Icc p₁ p₂, κ * f p * (1 - f p) ≤ f' p)
  (hleft : a ≤ f p₁) :
-- imply
  1 - Real.exp (-κ * a * (p₂ - p₁)) ≤ f p₂ := by
-- proof
  apply StatMech.BeffaraDC.thresholdLift_of_logisticDiffineq f f' hp hκ ha hf01 hderiv hdiff hleft

/--
[thresholdLift_logScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ThresholdLift.lean)
-/
@[path]
private lemma thresholdLift_logScale_eq
  {f f' : ℝ → ℝ}
  {p₁ p₂ c a : ℝ}
  {n : ℕ}
-- given
  (hp : p₁ ≤ p₂)
  (hc : 0 ≤ c)
  (ha : 0 < a)
  (hn : 1 ≤ n)
  (hf01 : ∀ p ∈ Icc p₁ p₂, f p ∈ Icc (0 : ℝ) 1)
  (hderiv : ∀ p ∈ Icc p₁ p₂, HasDerivAt f (f' p) p)
  (hdiff : ∀ p ∈ Icc p₁ p₂, c * Real.log (n : ℝ) * f p * (1 - f p) ≤ f' p)
  (hleft : a ≤ f p₁) :
-- imply
  1 - (n : ℝ) ^ (-c * a * (p₂ - p₁)) ≤ f p₂ := by
-- proof
  apply StatMech.BeffaraDC.thresholdLift_logScale f f' n hp hc ha hn hf01 hderiv hdiff hleft


-- created on 2026-10-23

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/PrekopaLeindler.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section

open MeasureTheory

open scoped ENNReal

namespace MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted

/-- The Prékopa–Leindler property for a measure `μ` on `E`: the integral
inequality holds for every `0 < t < 1` and all measurable `f g h` satisfying
the pointwise geometric-mean bound. -/
def PLProp (E : Type*) [Add E] [SMul ℝ E] [MeasurableSpace E]
    (μ : Measure E) : Prop :=
  ∀ {t : ℝ} (_ : 0 < t) (_ : t < 1) {f g h : E → ℝ≥0∞},
    Measurable f → Measurable g → Measurable h →
    (∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

end MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted
end

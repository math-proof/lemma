/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Integral/PrekopaLeindler.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

section

open MeasureTheory

open scoped ENNReal

namespace MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted

/-- The Prékopa–Leindler property for a measure `μ` on `E`: the integral
inequality holds for every `0 < t < 1` and all measurable `f g h` satisfying
the pointwise geometric-mean bound. -/
def PLProp (E : Type*) [Add E] [SMul ℝ E] [MeasurableSpace E]
    (μ : Measure E) : Prop :=
  ∀ {t : ℝ} (_ : 0 < t) (_ : t < 1) {f g h : E → ENNReal},
    Measurable f → Measurable g → Measurable h →
    (∀ x y : E, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

end MathlibExt.MeasureTheory.Integral.PrekopaLeindlerWanted
end
